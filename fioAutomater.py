__version__ = '0.2b0'  # PEP 440

# if fio is installed in a non-default location, change this to the fio path
fio = 'fio'

'''
Rewrite of the latency tester script from bash to Python with a lot of new features. (Thus the rename)
The test will run user defined scripts and report and parse the  results.
End goal is to be OS independent way to build, run, parse, and save fio test lists and results
and maybe long term to be able to measure power using a SeaJoule.
Created by George Seese
'''

# TODO: Add Dual LUN awareness

####### Code Table of Contents #######
### standard library imports
### class FioMinimalOut: used to decode fio minimal output into database and human readable format
### class System Commands: use these w/ OS.command to make command Windows/Linux agnostic
### class IOGeneratorInputs: workload objects return values ( fio_cmd, value_of_fio_cmd ), this gives each element an ID
### class Workload: defines fio properties; workloads are a list of objects made from this class
### class IOProperties: defines the properties of given rw= type (read/write, rand/seq, mixed r+w, cmd name, etc)
### function size_normalize: if given value with suffix (eg 4K, 1M, etc) calculate the byte value (base 1024)
### function compat_check: make sure all needed programs and libraries are installed; create list of warnings and errors
### function custom_workload_prompts: if file isn't loaded; this issues user prompts to create the WL
### function generate_workloads_list: takes user input and converts it to alist in a script usable format
### function display_workloads_list: does what it says (makes script format human readable)
### function drive_assigner: launches auto-assign if no drive given by -d; creates a job for each drive
### function job_builder: takes any created jobs; and adds them to every workload
### function run_fio_and_Save_results: does what it says on the tin
### function create_results_db: builds a database table with only the relevant info (leaves out unused options)
### function populate_results_db: inserts the workload details into the database table
### function parse_and_save_wlg_results: inserts the results of the workload run into the database table
### function workload_list_saver: saves a list of workloads to be run later, imports needed library
### function workload_list_loader: if -i is given, load the workload from the targeted file, imports a library
### function main: handles arg parsing and makes calls to relevant, non-looping fcts
######################################

### Section: Library imports #################################################
# Needed for test execution
import os
import time
import subprocess
import argparse
from distutils import spawn
import re
from collections import OrderedDict
from itertools import product

from copy import copy
# Needed for preparsing
import sqlite3


### End Section: Library imports ###############################################################

### Section:  fio minimal reader ###############################################
# Reads from fio minimal files
class FioMinimalOut(object):
    """use this class to pull the key values out of the fio -minimal output
    without needing to remember indexes"""

    # TODO: verify all these indexes on something other than fio 2.0.9
    def __init__(self, filename):
        # super(, self).__init__()
        self.filename = filename

    def jobname(self):
        return self.filename[2]

    def bw(self, operation):
        if 'read' in operation:
            return self.filename[6]
        elif 'write' in operation:
            return self.filename[47]
        else:
            return int(self.filename[6]) + int(self.filename[47])

    def iops(self, operation):
        if 'read' in operation:
            return self.filename[7]
        elif 'write' in operation:
            return self.filename[48]
        else:
            return int(self.filename[7]) + int(self.filename[48])

    def latency(self, operation, value):
        if 'read' in operation:
            return {
                'min':  self.filename[13],
                'max':  self.filename[14],
                'mean': self.filename[15],
                10:     self.filename[19].split('=')[1],
                20:     self.filename[20].split('=')[1],
                30:     self.filename[21].split('=')[1],
                40:     self.filename[22].split('=')[1],
                50:     self.filename[23].split('=')[1],
                60:     self.filename[24].split('=')[1],
                70:     self.filename[25].split('=')[1],
                80:     self.filename[26].split('=')[1],
                90:     self.filename[27].split('=')[1],
                95:     self.filename[28].split('=')[1],
                99:     self.filename[29].split('=')[1],
                99.5:   self.filename[30].split('=')[1],
                99.9:   self.filename[31].split('=')[1],
                99.95:  self.filename[32].split('=')[1],
                99.99:  self.filename[33].split('=')[1]
            }.get(value, "PctErr")
        elif 'write' in operation:
            return {
                'min':  self.filename[54],
                'max':  self.filename[55],
                'mean': self.filename[56],
                10:     self.filename[19].split('=')[1],
                20:     self.filename[20].split('=')[1],
                30:     self.filename[21].split('=')[1],
                40:     self.filename[22].split('=')[1],
                50:     self.filename[64].split('=')[1],
                60:     self.filename[65].split('=')[1],
                70:     self.filename[66].split('=')[1],
                80:     self.filename[67].split('=')[1],
                90:     self.filename[68].split('=')[1],
                95:     self.filename[69].split('=')[1],
                99:     self.filename[70].split('=')[1],
                99.5:   self.filename[71].split('=')[1],
                99.9:   self.filename[72].split('=')[1],
                99.95:  self.filename[73].split('=')[1],
                99.99:  self.filename[74].split('=')[1]
            }.get(value, "PctErr")
        else:
            if value == 'min':  # TODO: this calc shouldn't be done this way
                return min(float(self.filename[13]), float(self.filename[54]))
            elif value == 'max':  # nor should this
                return max(float(self.filename[14]), float(self.filename[55]))
            else:  # and definitely not this
                return float(self.filename[15]) + float(self.filename[56]) / 2


### End fio minimal reader ##############################################################

### Section:  OS dependent functions ##########################################
class SystemCommands(object):
    """Use this to issue commands that differ by OS. Each variable set via var_name = SystemCommands(os.name)
    should contain system info for the system it was called on"""
    # TODO: Restructure this so that list_drives, serial_num, and partition_check get called once

    def __init__(self, sys_type):

        print "Collecting drive and system info ..."
        self.SysType = sys_type

        # wmic os get Caption,CSDVersion /value
        # uname -a

        # TODO: test these changes
        self.luns_list = self.list_luns()
        self.partitioned_luns = self.partition_check()
        self.serial_number = {}
        for lun in self.luns_list:
            self.serial_number[lun] = self.serial_num(lun)

        # TODO: complete Dual LUN detection here
        self.drive_to_lun = {}
        # this will find cases where the serial numbers match, and pair them as 2+ LUNs on one drive
        # drive_to_lun has form {'SerialNumber': ['/dev/sdx', '/dev/sdy']}
        for lun_k, ser_num_v in self.serial_number.iteritems():
            if ser_num_v not in self.drive_to_lun.values():
                self.drive_to_lun[ser_num_v] = [lun_k]
            else:
                self.drive_to_lun[ser_num_v].append(lun_k)
        # takes the dictionary created and flatten it into a list for compat with old 1 LUN/drive assumption
        # TODO: decide if this is really the best way; or if keeping it as a dict is worth the effort to fix compat
        self.drive_list = [lun_pair for lun_pair in self.drive_to_lun.values()]

        if verbose_mode is True:
            # wmic os get Caption,CSDVersion /value
            print "Detected %s logical units" % len(self.luns_list)
            print "Detected %s logical units that contain partitions" % len(self.partitioned_luns)
            if len(self.drive_list) != len(self.luns_list):
                print "Detected logical unit/drive mismatch. Revising drives list..." \
                      "\nDetected %s drives" % len(self.drive_list)

    def clearscreen(self):
        return os.system('cls' if self.SysType == 'nt' else 'clear')

    def list_luns(self):

        if self.SysType == 'nt':  # for Windows
            # device = subprocess.check_output('wmic diskdrive get deviceid', shell=True).split()
            # for i in range(len(device)):
            #     if i != 0:
            #         devices.append(device[i])
            devices_unfiltered = subprocess.check_output('wmic diskdrive get deviceid', shell=True).splitlines()
            devices = [device.strip() for device in devices_unfiltered if device and 'DeviceID' not in device]

        else:  # for Linux
            devices = []
            for device in os.listdir("/dev/"):
                if device.startswith("sd") and not device[-1].isdigit():
                    devices.append(str('/dev/' + device))

        # sort works here, but not on the return
        devices.sort()

        return devices

    def serial_num(self, drive):
        # TODO: use these for Windows:  wmic diskdrive get index,deviceid,serialnumber,partitions
        # TODO: for single drive: wmic diskdrive 11 get serialnumber(but it returns the header)
        if self.SysType == 'nt':
            # device = subprocess.check_output('wmic diskdrive get deviceid', shell=True).split()
            # devices = []
            # for i in range(len(device)):
            #     if i != 0:
            #         devices.append(device[i])
            #         if drive == device[i]:
            #             return subprocess.check_output('wmic diskdrive get serialnumber').split()[i]

            drive_number = ''.join(char for char in drive if char.isdigit())
            wmic_string = 'wmic diskdrive %s get serialnumber' % drive_number

            unfiltered_sernum = subprocess.check_output(wmic_string, shell=True).splitlines()

            serial_number = [sernum.strip() for sernum in unfiltered_sernum if sernum and 'SerialNumber' not in sernum]

            return serial_number[0]

        else:
            # TODO: Test: udevadm info --query=all --name=/dev/sdc | grep ID_SERIAL_SHORT for SATA
            # TODO: Test: udevadm info --query=all --name=/dev/sdd | grep ID_SCSI_SERIAL for SAS
            try:
                p1 = subprocess.Popen(["smartctl", "-i", "%s" % drive], stdout=subprocess.PIPE)
                p2 = subprocess.Popen(["grep", "Serial"], stdin=p1.stdout, stdout=subprocess.PIPE)
                p1.stdout.close()
                out, err = p2.communicate()
                try:
                    serial = out.split(":")[1].strip()[0:8]
                except IndexError:
                    serial = 'SerNumErr'

            except OSError:
                try:  # only works for drives through HBA; figure out how to choose the right one if it's on SATA
                    p1 = subprocess.Popen(["udevadm", "info", "--query=all", "--name=%s" % drive],
                                          stdout=subprocess.PIPE)
                    p2 = subprocess.Popen(["grep", "ID_SCSI_SERIAL"], stdin=p1.stdout, stdout=subprocess.PIPE)
                    p1.stdout.close()
                    out, err = p2.communicate()
                    serial = out.split("=")[1].strip()[0:8]
                except OSError:
                    serial = "SerNumErr"

                except IndexError:
                    #  this might be able to catch drives hooked up via SATA port
                    p1 = subprocess.Popen(["udevadm", "info", "--query=all", "--name=%s" % drive],
                                          stdout=subprocess.PIPE)
                    p2 = subprocess.Popen(["grep", "ID_SERIAL_SHORT"], stdin=p1.stdout, stdout=subprocess.PIPE)
                    p1.stdout.close()
                    out, err = p2.communicate()
                    try:
                        serial = out.split(":")[1].strip()[0:8]
                    except IndexError:
                        serial = 'SerNumErr'

            return serial

    def write_cache(self, drive, cache_state):
        def change_state(parm_val, smartctl_val, drive, cache_status):
            if self.SysType == "nt":
                # TODO: Search for SeaChest
                pass
            else:
                try:
                    p1 = subprocess.call(['sdparm', '-s', 'WCE=%s' % parm_val, '%s' % drive])
                except OSError:
                    try:
                        p1 = subprocess.call(['smartctl', '-s', 'wcache,%s' % smartctl_val, '%s' % drive])
                    except OSError:
                        try:
                            p1 = subprocess.call(['hdparm', '-W%s' % parm_val, '%s' % drive])
                        except OSError:
                            # TODO: put SeaChest here
                            pass
            # subprocess.call should return p1=0 on success
            if p1 != 0:
                print cache_status

        if cache_state is True:
            parm_val = '1'
            smartctl_val = 'on'
            cache_status = "Failed to enable write cache on %s" % drive
            change_state(parm_val, smartctl_val, drive, cache_status)
        elif cache_state is False:
            parm_val = '0'
            smartctl_val = 'off'
            cache_status = "Failed to disable write cache on %s" % drive
            change_state(parm_val, smartctl_val, drive, cache_status)
        else:
            # ends up here if no change is requested (or something weird happens)
            pass

    def partition_check(self):
        if self.SysType == "nt":

            # TODO: Test it thoroughly
            devs_unfiltered = subprocess.check_output('wmic diskdrive get deviceid,partitions', shell=True).splitlines()
            filtered_devs = [dev.strip() for dev in devs_unfiltered if dev and 'DeviceID' not in dev]

            parted_devices = []
            for f_dev in filtered_devs:
                dev_tuple = tuple(f_dev.split())

                if len(dev_tuple) > 1:  # if partitions didn't report, length is 1
                    if int(dev_tuple[1]) != 0:  # partitions returns num of partitions; 0 means unpartitioned
                        parted_devices.append(dev_tuple[0])
                else:  # append drives that failed to list as a safety precaution
                    parted_devices.append(dev_tuple[0])

            # TODO: windows can return no status for partition; that causes index error here; if that can be caught the
            # TODO: cont: whole complex thing above can use the one liner below
            # TODO: try this: [pdev.split()[0] for pdev in filtered_devs if pdev.split()[1] or pdev.split()[1] != 0]
            # parted_devices = [pdev.split()[0] for pdev in filtered_devs if pdev.split()[1] != 0]

            return set(parted_devices)

        else:
            # parted_devices = []
            # for device in os.listdir("/dev/"):
            #     if device.startswith("sd") and device[-1].isdigit():
            #         parted_device = filter(lambda x: x.isalpha(), device)
            #         parted_devices.append(str('/dev/' + parted_device))
            # TODO: changed this to use list comprehension. py 2to3 cannot do the lambda propery

            def digit_remove(in_string):
                """py 2to3 doesn't read the lambda properly. This is a conversion to a proper function"""
                cleaned_string = ''.join(char for char in in_string if not char.isdigit())
                return cleaned_string

            parted_devices = [str('/dev/' + digit_remove(device)) for device in os.listdir('/dev/')
                              if device.startswith('sd') and device[-1].isdigit()]

            return set(parted_devices)


### End Section: OS dependent fcts ##############################################################


class IOGeneratorInputs(object):

    all_io_commands = []

    def __init__(self, cmd, val, norm=None):
        self.cmd = cmd
        self.value = val
        self.normal = norm

        # This will save a list of all IO params that the object has seen (maybe)
        IOGeneratorInputs.all_io_commands.append(self)

    def io_command(self):
        return self.cmd

    def io_value(self):
        return self.value

    def io_normalized(self):
        return self.normal


# TODO: Use the link to create a setup that allows IOMeter or fio
# https://stackoverflow.com/questions/40898482/defining-method-of-class-in-if-statement

# Use this to allow on the fly creating of new methods
# https://stackoverflow.com/questions/17929543/how-can-i-dynamically-create-class-methods-for-a-class-in-python
# Use this to allow optional arguments in the __init__
# https://stackoverflow.com/questions/8187082/how-can-you-set-class-attributes-from-variable-arguments-kwargs-in-python
# https://stackoverflow.com/questions/3884612/automatically-setting-class-member-variables-in-python
class Workload(object):
    """Each fio workload to be run should be an instance of this Workload object
       Returns from methods should all be 'return fio_command, fio_cmd_value, *additional_properties' """

    # define here lists of fio params that apply only to certain cases
    write_unique = ["write_cache_setting"]
    mixed_unique = ["rwmixread", "rwmixwrite"]
    random_unique = ["percentage_random"]

    # Define here anything that shouldn't be added to fio commands
    non_wlg_commands = ["write_cache_setting"]

    # Define any items that shouldn't print to the display list
    skip_display = ['startdelay', 'bwavgtime', 'ioengine']

    # this will update with all params that have ever been modified (for all WLs ever(no idea how that works))
    all_io_gen_commands = []

    # this will track every attribute that has ever been defined as an fio global
    global_io_gen_commands = []

    def __init__(self, jobname=None, readwrite=None, queue_depth=None, blocksize=None,
                 read_percent=None, write_percent=None, percent_random=None, run_time=None,
                 ramp_time=None, enable_write_cache=None, io_target=None, zone_mode=None,
                 io_engine=None, start_delay=None, bw_avg_time=None, group_report=False):
        """Initialize all to None unless otherwise specified"""
        ## self.workload_index = workload_index
        self.job = jobname
        # self._iodepth = queue_depth
        # self._rw = readwrite
        # self._bs = blocksize
        # self._rwmixread = read_percent
        # self._rwmixwrite = write_percent
        # self._percentage_random = percent_random
        # self._runtime = run_time
        # self._ramp_time = ramp_time

        # this will track each workload command that has been set for the current workload
        self.wl_gen_commands = []

        # these are calls to the setter functions which ensure that the wl_gen_commands gets appended correctly
        # Name must come first as fio treats it as a divider
        self.name = jobname

        # The order that these are in will be the order of the display fct columns
        self.filename = io_target
        self.rw = readwrite
        self.bs = blocksize
        self.iodepth = queue_depth
        self.rwmixread = read_percent
        self.rwmixwrite = write_percent
        self.percentage_random = percent_random
        # This is the write cache setting for the workload. (True/False or None) This one doesn't get passed to fio
        self.write_cache_setting = enable_write_cache
        self.runtime = run_time
        self.ramp_time = ramp_time
        self.ioengine = io_engine
        self.zonemode = zone_mode
        self.startdelay = start_delay
        self.bwavgtime = bw_avg_time
        self.group_reporting = group_report

    def __eq__(self, other):
        """This allows two workload objects to be compared"""
        return self.__dict__ == other.__dict__

    @property
    def name(self):
        """Get the current jobname"""
        return IOGeneratorInputs('name', self._name)

    @name.setter
    def name(self, jobname):
        """Set the current jobname"""
        self._name = jobname
        if self._name != 'global':
            self._io_list_appender('name', self._name)

    @property
    def rw(self):
        """Get the workload to be run"""
        # print "reading rw"
        return IOGeneratorInputs('rw', self._rw)

    @rw.setter
    def rw(self, readwrite):
        """Set the workload to be run"""
        # print "rw set to %s" % readwrite
        self._rw = readwrite
        # if self._rw is not None:
        #     self._io_list_appender('rw')
        #     # Workload.all_io_gen_commands.append('rw')
        #     # self.wl_gen_commands.append('rw')
        self._io_list_appender('rw', self._rw)

    @property
    def bs(self):
        """Get the blocksize to be run, and calculate the integer value of that blocksize"""
        # bs_int = size_normalize(self._bs)
        # return IOGeneratorInputs('bs', self._bs, bs_int)
        # Right now I don't use the integer value from here anywhere, save the calc time by skipping it
        return IOGeneratorInputs('bs', self._bs)

    @bs.setter
    def bs(self, blocksize):
        """Set the blocksize to be run"""
        self._bs = blocksize
        # if self._bs is not None:
        #     self._io_list_appender('bs')
        #     # Workload.all_io_gen_commands.append('bs')
        #     # self.wl_gen_commands.append('bs')
        self._io_list_appender('bs', self._bs)

    @property
    def iodepth(self):
        """Get the queue depth to be run"""
        return IOGeneratorInputs('iodepth', self._iodepth)

    @iodepth.setter
    def iodepth(self, queue_depth):
        """Set the queue depth to be run"""
        try:
            self._iodepth = int(queue_depth)
        except ValueError:
            # print "Queue depth %s invalid. Must be an integer value. Will default to 1." % queue_depth
            self._iodepth = None
        except TypeError:
            # print "Queue depth %s invalid. Must be an integer value. Will default to 1." % queue_depth
            self._iodepth = None

        # if self._iodepth is not None:
        #     self._io_list_appender('iodepth')
        self._io_list_appender('iodepth', self._iodepth)

    @property
    def rwmixread(self):
        """Get the percentage of workload expected to be reads"""
        return IOGeneratorInputs('rwmixread', self._rwmixread)

    @rwmixread.setter
    def rwmixread(self, read_percent):
        """Set the percentage of workload to be reads. This should be mutually exclusive with percentwrite"""
        try:
            self._rwmixread = int(read_percent)
        except ValueError:
            # print "Read percentage %s is invalid. Must be integer. Defaulting to 'None'" % read_percent
            self._rwmixread = None
        except TypeError:
            # print "Read percentage %s is invalid. Must be integer. Defaulting to 'None'" % read_percent
            self._rwmixread = None

        # if self._rwmixread is not None:
        #     # if 'rwmixread' not in Workload.all_io_gen_commands:
        #     #     Workload.all_io_gen_commands.append('rwmixread')
        #     # self.wl_gen_commands.append('rwmixread')
        #     self._io_list_appender('rwmixread')
        self._io_list_appender('rwmixread', self._rwmixread)

    @property
    def rwmixwrite(self):
        """Get the percentage of workload expected to be writes"""
        return IOGeneratorInputs('rwmixwrite', self._rwmixwrite)

    @rwmixwrite.setter
    def rwmixwrite(self, write_percent):
        """Set the percentage of workload to be write. This should be mutually exclusive with percentread"""
        try:
            self._rwmixwrite = int(write_percent)
        except ValueError:
            # print "Write percentage %s is invalid. Must be integer. Defaulting to 'None'" % write_percent
            self._rwmixwrite = None
        except TypeError:
            # print "Write percentage %s is invalid. Must be integer. Defaulting to 'None'" % write_percent
            self._rwmixwrite = None

        # if self._rwmixwrite is not None:
        #     self._io_list_appender('rwmixwrite')
        self._io_list_appender('rwmixwrite', self._rwmixwrite)

    @property
    def percentage_random(self):
        """Get the percentage of workload that should be random (vs sequential)"""
        return IOGeneratorInputs('percentage_random', self._percentage_random)

    @percentage_random.setter
    def percentage_random(self, rand_pct):
        """Set the percentage of random workload. Only settable when rw=randoms. 100%=full rand, 0%=full seq"""
        self._percentage_random = rand_pct

        # if self._percentage_random is not None:
        #     self._io_list_appender('percentage_random')
        self._io_list_appender('percentage_random', self._percentage_random)

    @property
    def runtime(self):
        """Get the runtime of each workload"""
        return IOGeneratorInputs('runtime', self._runtime)

    @runtime.setter
    def runtime(self, run_time):
        """Set the runtime of each workload. Default is seconds. Newer fio versions will allow suffixes so I will too"""
        self._runtime = run_time

        # if self._runtime is not None:
        #     self._io_list_appender('runtime')
        self._io_list_appender('runtime', self._runtime)

    @property
    def ramp_time(self):
        """Get the ramp_time of each workload. This is the time the script is running I/O but not recording data"""
        return IOGeneratorInputs('ramp_time', self._ramp_time)

    @ramp_time.setter
    def ramp_time(self, ramp_time):
        """Set the ramp_time. New fio allows suffixes; may eventually want a time normalizer"""
        self._ramp_time = ramp_time

        if str(self._ramp_time).strip() is not "0":
            # only add ramptime to the calls if it is not 0
            self._io_list_appender('ramp_time', self._ramp_time)

    @property
    def filename(self):
        """Get the target/filename"""
        return IOGeneratorInputs('filename', self._filename)

    @filename.setter
    def filename(self, io_target):
        """Set the drive/ filename to target here"""
        self._filename = io_target
        self._io_list_appender('filename', self._filename)

    @property
    def zonemode(self):
        """Setting zonemode=zbd allows testing on SMR devices. Get the zonemode value"""
        return IOGeneratorInputs('zonemode', self._zonemode)

    @zonemode.setter
    def zonemode(self, zone_mode):
        """Setting zonemode=zbd allows testing on SMR devices. Set the zonemode value; and only append in cases where it
        is set to zbd"""
        self._zonemode = zone_mode
        self._io_list_appender('zonemode', self._zonemode)

    @property
    def ioengine(self):
        """Use to get the ioengine to use. """
        # TODO: Currently is manually inserted into the fio command line; move it here
        return IOGeneratorInputs('ioengine', self._ioengine)

    @ioengine.setter
    def ioengine(self, io_engine):
        """Use to set the ioengine to use. Has OS dependence """
        self._ioengine = io_engine
        self._io_list_appender('ioengine', self._ioengine)

    @property
    def startdelay(self):
        """Get the time to delay the job start by this amount."""
        # TODO: could be used as a replacement for current wait time implementation
        return IOGeneratorInputs('startdelay', self._startdelay)

    @startdelay.setter
    def startdelay(self, start_delay):
        """Set the amount of time to delay job start"""
        self._startdelay = start_delay
        self._io_list_appender('startdelay', self._startdelay)

    @property
    def bwavgtime(self):
        """Get the time interval that fio should average bw readings across"""
        return IOGeneratorInputs('bwavgtime', self._bwavgtime)

    @bwavgtime.setter
    def bwavgtime(self, bw_avg_time):
        """Set the time interval that fio should average bw readings across"""
        self._bwavgtime = bw_avg_time
        self._io_list_appender('bwavgtime', self._bwavgtime)

    @property
    def group_reporting(self):
        """Get group reporting status, if it is set all jobs will report as one unless split by new group"""
        return IOGeneratorInputs('group_reporting', self._group_reporting)

    @group_reporting.setter
    def group_reporting(self, group_report):
        """Set group reporting status, if it is set all jobs will report as one unless split by new group"""
        if group_report is True:
            self._group_reporting = 1
            self._io_list_appender('group_reporting', self._group_reporting)

    @property
    def new_group(self):
        """Split the results reporting into groups instead of by every job"""
        return IOGeneratorInputs('newgroup', self._new_group)

    @new_group.setter
    def new_group(self, create_group):
        """Set this True to add new_group to the job"""
        if create_group is True:
            self._new_group = 1
            self._io_list_appender('new_group', self._new_group)

    @property
    def write_cache_setting(self):
        """return the write cache setting"""
        # Return None to indicate it isn't an fio command to the command line builder
        return IOGeneratorInputs(None, self._write_cache_enabled)

    @write_cache_setting.setter
    def write_cache_setting(self, write_cache_enabled):
        """Set the write cache setting."""
        self._write_cache_enabled = write_cache_enabled
        self._io_list_appender('write_cache_setting', self._write_cache_enabled)

    def _io_list_appender(self, iog_command, iog_value):
        """This function makes sure that each workload and the overall Workloads list each correctly assign the
        io program commands to the correct lists. It also makes sure items that were previously set to value other
        than None get removed if they are later changed to None.
         Called within the class define only"""
        # Don't actually remove the Nones or spacing goes wrong
        if iog_value is not None:
            """Add it if it's not None"""

            # Adds it to the list that tracks every command that's been set
            if iog_command not in Workload.all_io_gen_commands:
                Workload.all_io_gen_commands.append(iog_command)

            # Adds it to the list that tracks if it's been on this specific workload
            if iog_command not in self.wl_gen_commands:
                self.wl_gen_commands.append(iog_command)

            # Add it to the list that tracks if it's been set as a global for this workload
            if iog_command not in self.global_io_gen_commands and self.name.io_value() == 'global':
                self.global_io_gen_commands.append(iog_command)

        # if iog_value is None:
        #     """remove it if it is None"""
        #     self.wl_gen_commands[:] = [x for x in self.wl_gen_commands if x != iog_command]


# https://stackoverflow.com/questions/33072570/when-should-i-be-using-classes-in-python
# https://jeffknupp.com/blog/2014/06/18/improve-your-python-python-classes-and-object-oriented-programming/
# https://tomayko.com/blog/2005/getters-setters-fuxors
# https://stackoverflow.com/questions/22497985/is-it-a-bad-idea-to-define-a-local-class-inside-a-function-in-python

class IOProperties(object):
    """When creating the workload options dictionary, this class can be used to add new executable I/O types
    Is defined inside custom_workload_prompts function (add new workloads there)
    Is used inside custom_workload_prompts function and wl_constructor function"""

    def __init__(self, io_active, display_desc, fio_io, random_io, mixed_io, write_io):
        """Should be bool, string, string, bool, bool"""
        self.io_active = io_active
        self.display_desc = display_desc
        self.fio_io = fio_io
        self.random_io = random_io
        self.mixed_io = mixed_io
        self.write_io = write_io

    @property
    def add_io(self):
        """Return whether the current IO is set to execute"""
        return self.io_active

    @add_io.setter
    def add_io(self, io_act_state):
        """Change whether the current IO is set to execute"""
        self.io_active = io_act_state

    def plain_text_desc(self):
        """Get the plain english description of the workload. This is what is displayed to the user"""
        return self.display_desc

    def fio_rw_val(self):
        """Return the X value that fio's rw=X should be set to for the given I/O type"""
        return self.fio_io

    def is_random(self):
        """Return whether the I/O type is random"""
        return self.random_io

    def is_mixed(self):
        """Return whether the I/O type is mixed workloads"""
        return self.mixed_io

    def is_writes(self):
        """ Return whether the I/O type issues writes (including mixed read/writes)"""
        return self.write_io


def size_normalize(input_size):
    """when given a blocksize or filesize with suffixes, this will return their integer value"""

    try:
        size_int = int(input_size)
    except ValueError:
        # If it's not an int, make one based on the suffix
        # splits by integer and fio accepted size followers, ignore anything else
        size_split = filter(None, re.split(r"(\d+)([KMGkmg]{1})", str(input_size)))
        # cycle through each split value, and multiply the previous by correct amount per suffix
        # for bs=xK, bs=xM, etc there will be 2 here; for bs=xK,yK there will be 5
        for index, value in enumerate(size_split):
            if size_split[index].upper() == "K":
                size_split[index - 1] = int(size_split[index - 1]) * 1024
            elif size_split[index].upper() == "M":
                size_split[index - 1] = int(size_split[index - 1]) * 1024 * 1024
            elif size_split[index].upper() == "G":
                size_split[index - 1] = int(size_split[index - 1]) * 1024 * 1024 * 1024
            elif size_split[index].upper() == "T":
                size_split[index - 1] = int(size_split[index - 1]) * 1024 * 1024 * 1024 * 1024

        # TODO: decide if/how to do split bs values beyond the first
        # for now this only captures (and therefore enables sorts) on the first bs_split value
        size_int = size_split[0]

    return size_int


def compat_check(env):
    """ use this function to verify that all the necessary tools and items are installed on the system
    this might be best moved from it's own fct to the main fct since it won't be called more than once"""

    warnings_list = []
    errors_list = []
    # verify that fio is installed, the script is useless without it.
    # Also get version number and check against versions with known issues
    try:
        fioversion = subprocess.Popen([fio, "-v"], stdout=subprocess.PIPE).communicate()[0]
        print "fio version: %s" % fioversion
        # check for the versions that had a log bug

        '''#IDEA: I don't actually use the log anymore... just chuck this?
        #this ugly if statement looks for everything after the last . if fio v2.1.x is found
        if 6 <= re.findall('fio-2.1.\d+', fioversion)[0].rsplit('.')[1] <= 12
            warnings_list.append("fio versions 2.1.6 to 2.1.12 have had logging issues in tests.")
        '''
    except OSError:
        # TODO: Maybe: Create symlink when sudo for user? Otherwise fio often can't be found
        errors_list.append("No fio install found. Please install fio.")

    # Check user privileges, fio usually requires root access to run; euid only valid in Linux
    if env == 'posix' and not os.geteuid() == 0:
        errors_list.append(
            "You are not root; fio often requires root privileges to run.\n    Please try again as root or using 'su'")

    # Check for smartctl (Serial number and cache tool)
    smartctlpath = spawn.find_executable("smartctl")

    # check for udevadm (Serial num tool)
    udevadmpath = spawn.find_executable("udevadm")

    # Check for sdparm (cache tool)
    sdparmpath = spawn.find_executable("sdparm")

    # Check for hdparm
    hdparmpath = spawn.find_executable("hdparm")

    # TODO: Check for SeaChest (probably regex it)

    # Check all Serial number tools
    # TODO may add alternate methods later (sg_inq, hdparm -I)
    if smartctlpath is None and udevadmpath is None:
        warnings_list.append(
            "No serial number tool. Serial numbers will not save properly.\n   Install smartctl or udevadm to fix.")

    # Check all viable SAS cache tools
    if sdparmpath is None:
        warnings_list.append(
            "No supported SAS write cache tool found. SAS cache cannot be altered.\n   Install sdparm to fix.")
    # Check for all viable SATA cache tools
    if hdparmpath is None and sdparmpath is None and smartctlpath is None:
        warnings_list.append(
            "No supported SATA write cache tool found. SATA cache state cannot be altered.\n"
            "   Install sdparm, smartctl, or hdparm to fix.")

    # Summarize all the warnings and errors
    if len(warnings_list) > 0:
        print "\n\n!!!!!!! WARNING(S) FOUND !!!!!!!"
        print "**Found %s possible issue(s):" % len(warnings_list)
        for warning in warnings_list:
            print warning
        print "Program will run with these issues, but behavior may not be as expected."
        raw_input("Press [Enter] to continue...")
    if len(errors_list) > 0:
        print "\n\n!!!!!!! CRITICAL ERROR(S) !!!!!!"
        print "**Found %s critical issue(s):" % len(errors_list)
        for error in errors_list:
            print error
        print "Must resolve critical error(s) listed above to continue"
        quit(1)


def custom_workload_prompts(advanced_prompts_enabled, zone_mode_enabled):
    """This fct is used to gather user input via prompt to build the final workloads"""

    # wl_matrix_builder will contain all the stuff that needs to be iterated to build the workload list
    # key = fio command, value = input to fio command
    wl_matrix_builder = OrderedDict()

    workload_opts_dict = OrderedDict()
    # dictionary is used to toggle the workload choices. New options can be added here (ie Trim)
    # The dict key is the key the user will press to toggle that workload
    workload_opts_dict['R'] = IOProperties(True, 'Random Read Testing', 'randread', True, False, False)
    workload_opts_dict['W'] = IOProperties(True, 'Random Write Testing', 'randwrite', True, False, True)
    workload_opts_dict['M'] = IOProperties(False, 'Random Mixed I/O Testing', 'randrw', True, True, True)
    workload_opts_dict['X'] = IOProperties(False, 'Sequential Read Testing', 'read', False, False, False)
    workload_opts_dict['Y'] = IOProperties(False, 'Sequential Write Testing', 'write', False, False, True)
    workload_opts_dict['Z'] = IOProperties(False, 'Sequential Mixed I/O Testing', 'rw', False, True, True)

    user_input_workload = ""

    while "C" not in user_input_workload:
        OS.clearscreen()

        print """Add one or more letters followed by [enter] to toggle the corresponding option(s).
        The prompt will remain active and accept selections until [C] or [Q] is included in the input.
        This prompt is NOT case sensitive.
        Press [C] then [enter] to confirm or [Q] then [enter] to quit.\n---Current Selections---"""

        for wod_key in workload_opts_dict.keys():
            # ugly looking print spits out all valid I/O options and makes sure everything stays aligned
            print "[{!s:<5}] {:<1}: {!s}".format(workload_opts_dict[wod_key].add_io, wod_key,
                                                 workload_opts_dict[wod_key].plain_text_desc())
        user_input_workload = raw_input("Input a key(s): ").upper()

        for letter in user_input_workload:
            if letter in workload_opts_dict:
                workload_opts_dict[letter].add_io = not workload_opts_dict[letter].add_io

        if "Q" in user_input_workload:
            print "Quitting due to keystroke..."
            quit(0)

    else:  # do the below after 'C' is pressed
        # quit if no workloads have been set as active after [c] is pressed
        if all(value.add_io is False for value in workload_opts_dict.values()):
            print "Quitting since no workloads were set as active..."
            quit(2)

    # WC setting prompts
    wc_entry = {}
    for write_key_check in workload_opts_dict.keys():
        if workload_opts_dict[write_key_check].add_io is True \
                and workload_opts_dict[write_key_check].is_writes() is True:
            while True:
                valid_wc_keys = ['E', 'D', 'B', 'N', 'Q']
                print ("Choose the desired Write Cache setting for %s. Valid options are:"
                       "\n[E]: Enabled"
                       "\n[D]: Disabled"
                       "\n[B]: Both. Will run once enabled, then once disabled"
                       "\n[N]: No change. The script will not issue any set write cache commands."
                       ) % workload_opts_dict[write_key_check].display_desc
                wc_entry[workload_opts_dict[write_key_check].fio_rw_val()] = raw_input("Enter a selection. [Q] will quit: ").upper()

                if wc_entry[workload_opts_dict[write_key_check].fio_rw_val()] not in valid_wc_keys:
                    print "Invalid choice, try again..."
                elif "Q" in wc_entry[workload_opts_dict[write_key_check].fio_rw_val()]:
                    print "Quitting due to keystroke..."
                    quit(0)
                else:
                    break

    # Blocksize prompts
    print "Type the block sizes to run separated with a space. Will accept suffixes such as K, M, G."
    print "Press [enter] when done, or press [q] then [enter] to quit test setup."
    blocksize_entry = raw_input("Block sizes: ").upper()

    if 'Q' in blocksize_entry:
        print "Quitting due to keystroke..."
        quit(0)

    if 'to' in blocksize_entry:
        # TODO: Logic to create a list from low to high
        print "That functionality isn't finished yet..."
        quit(2)
    else:
        # Split block size input into list by white space
        wl_matrix_builder['bs'] = blocksize_entry.split()

    # Queue depth tests
    print "Type the Queue depths to run separated with a space. "
    print "Press [enter] when done, or press [q] then [enter] to quit test setup."
    qd_valid = False
    while qd_valid is False:
        queue_depth_entry = raw_input("Queue depths: ")
        if 'Q' in queue_depth_entry or 'q' in queue_depth_entry:
            print "Quitting due to keystroke..."
            quit(0)
        if 'to' in queue_depth_entry:
            # TODO: Logic to step from low to high; when that's done change qd_valid = True
            qd_valid = False
        else:
            wl_matrix_builder['iodepth'] = queue_depth_entry.split()
            for queue_depth in wl_matrix_builder['iodepth']:
                try:
                    int(queue_depth)
                    qd_valid = True
                except ValueError:
                    print "%s is invalid. Queue depth must be an integer value" % queue_depth
                    qd_valid = False

    # Mixed workload read percentages
    # Check to see if WL types marked with mixed IO = True are also marked as run = True
    # TODO: There could be fct potential here (and with queue depth)
    for wod_key in workload_opts_dict.keys():
        if workload_opts_dict[wod_key].is_mixed() is True and workload_opts_dict[wod_key].add_io is True:
            print "Type the percentage reads to be use in %s testing, separated by a space." % workload_opts_dict[
                wod_key].display_desc
            print " Press [enter] when done, or press [q] then [enter] to quit test setup."
            rp_valid = False
            while rp_valid is False:
                read_percentages_entry = raw_input("Read Percentages: ")
                if 'Q' in read_percentages_entry or 'q' in read_percentages_entry:
                    print "Quitting due to keystroke..."
                    quit(0)
                wl_matrix_builder['rwmixread'] = read_percentages_entry.split()
                for read_mix in wl_matrix_builder['rwmixread']:
                    try:
                        int(read_mix)
                        rp_valid = True
                    except ValueError:
                        print "%s is invalid. Read percentages must be an integer value" % read_mix
                        rp_valid = False

    # TODO: Put any SMR specific options here
        if zone_mode_enabled is True:
            wl_matrix_builder['zonemode'] = True

    # TODO: Advanced options below
    if advanced_prompts_enabled is True:
        pass
        # Percentage Random

        # Sequential by size (instead of time)

        # Sequential by zone (instead of continuous)

        # High PRIO percentages

        # Custom

        # By job prompts (allow things to get really customized by job)
        # Will probably require a nested fct of Workload class

    return workload_opts_dict, wl_matrix_builder, wc_entry


def generate_workloads_list(wl_defines, wl_matrix, wc_settings, runtime, ramptime):
    """build the list of workloads based on the user inputs in custom_workload_prompts
    The final data structure here will be a list of list where outer list is each workload
    and inner list is each job for the given workload."""
    # wl_defines is passed in from workload_opts_dict, wl_matrix is wl_matrix_builder, wc_settings is wc_entry

    # This will create a matrix of every possible value combination, including ones that aren't wanted
    # TODO: Figure out if there's a way to create only the desired ones
    fio_values_set = []
    fio_param_list = wl_matrix.keys()

    # Use this to get rw as an object... this will allow use of .is_writes, .is_mixed, and .is_random later
    fio_rw_vals = []
    for io_type in wl_defines.values():
        if io_type.add_io is True:
            fio_rw_vals.append(io_type)

    # Use this to get every fio parameter EXCEPT rw
    for fio_param in fio_param_list:
        fio_values_set.append(wl_matrix[fio_param])

    # Insert the rw values at the head of the list, they should cycle first
    fio_param_list.insert(0, 'rw')
    fio_values_set.insert(0, fio_rw_vals)

    # this statement cartesian products everything in the lists; it is the engine that makes this fct work
    wl_list = list(product(*fio_values_set))

    # Save the final wl list as a list of objects in this list
    wl_list_of_objects = []

    # Each workload will consist of a [global] job and one or more other jobs; use this to store them
    list_of_jobs = []

    # This converts the list of tuples into a list of objects
    for wl_obj_num, wl in enumerate(wl_list):
        # this basically just creates a new empty Workload object for each workload to be run
        # TODO: figure out if there's a better way to do runtime and ramptime
        wl_list_of_objects.append(Workload('global', run_time=runtime, ramp_time=ramptime))

        for index, fio_cmd in enumerate(wl):
            # the .rw attr will be set to the IOProperties object; see comment a few above
            setattr(wl_list_of_objects[wl_obj_num], fio_param_list[index], fio_cmd)

    # this set of loops will tweak workloads for cases where a fio parameter was assigned to a workload it shouldn't be
    final_wl_list = []
    intermediate_wl_list = []
    for wl_index, wl_object in enumerate(wl_list_of_objects):
        """step through every workload in the list"""

        # by default, don't duplicate workloads
        add_duplicate_for_wc = False

        for param in fio_param_list:
            """step through every parameter per workload (ie rw, bs, iodepth, etc)"""

            if param is 'rw':
                """put checks for .is_writes, .is_random, and .is_mixed here and modify the workload accordingly"""
                # .io_command() and .io_value() are defined in IOGeneratorInputs(object)
                write_check = getattr(wl_object, param).io_value().is_writes()
                random_check = getattr(wl_object, param).io_value().is_random()
                mixed_check = getattr(wl_object, param).io_value().is_mixed()
                fio_readwrite = getattr(wl_object,param).io_value().fio_rw_val()

                # handle write cache settings here
                if fio_readwrite in wc_settings.keys():

                    if wc_settings[fio_readwrite] == "E":
                        setattr(wl_object, 'write_cache_setting', True)
                    elif wc_settings[fio_readwrite] == "D":
                        setattr(wl_object, 'write_cache_setting', False)
                    elif wc_settings[fio_readwrite] == "B":
                        # set the current workload to WCD
                        setattr(wl_object, 'write_cache_setting', False)
                        # set this so that the end of the loop knows we want another copy (see below)
                        add_duplicate_for_wc = True
                    else:
                        setattr(wl_object, 'write_cache_setting', None)

                    # TODO: delete print
                    # print wl_object.write_cache_setting

                # TODO: DEBUG: delete print
                # print getattr(wl_object, param).io_command(), getattr(wl_object, param).io_value().fio_rw_val(),
            else:

                # delete anything that should only apply to randoms from non-random WLs
                if random_check is False and param in wl_object.random_unique:
                    setattr(wl_object, param, None)

                # delete anything that should only apply to mixed workloads from non-mixed workloads
                if mixed_check is False and param in wl_object.mixed_unique:
                    # TODO: delete print
                    # print "Removing",
                    # TODO: figure out why delattr won't work
                    # delattr(wl_object, param)
                    setattr(wl_object, param, None)

                # TODO: DEBUG: delete print
                # print getattr(wl_object, param),

        # TODO: DEBUG: delete print
        # print id(wl_object)

        # this will only add the generated workload to the final_wl_list if an identical workload object
        # doesn't already exist.
        # Doing this is necessary as duplicates will be created when there is a fio-cmd that doesn't
        # apply to all workloads (ie adding mixed rw percentages will cause duplicates of non-mixed wls)
        if wl_object not in final_wl_list:
            final_wl_list.append(wl_object)

        # add the duplicate for write cache = 'B' here, otherwise it goes infinite loop
        if add_duplicate_for_wc is True:

            # create a copy of the object to mess with, rather than a reference or things get weird
            new_wl_object = copy(wl_object)

            # set it opposite the current setting
            new_wl_object.write_cache_setting = not new_wl_object.write_cache_setting.value

            # append the copy to the list if it doesn't already exist there
            if new_wl_object not in final_wl_list:
                final_wl_list.append(new_wl_object)

    # TODO: delete print
    # print "%s workloads created" % len(wl_list_of_objects)
    # print "%s workloads kept" % len(final_wl_list)

    return final_wl_list  # , fio_param_list


def isp_mode(fan_command, fan_speeds, isp_runtime, isp_ramp_time):
    """if the user enters -I or --ISPtest then use this to set up the workloads to run list"""

    # TODO: Add baseline case to run before fans start up. Should be one drive under write test
    # TODO: Figure out how to handle Dual LUN

    isp_workload_list = []
    isp_global_list = []

    # The IO defines have extra properties in order to allow proper setting of things like WC
    # in order to use the same fcts throughout, ISP mode must alsouse the advanced defines
    workload_details_dict = {'R': IOProperties(True, 'Random Read Testing', 'randread', True, False, False),
                             'W': IOProperties(True, 'Random Write Testing', 'randwrite', True, False, True),
                             'Y': IOProperties(True, 'Sequential Write Testing', 'write', False, False, True),
                             }

    print "Running in ISP mode. Many options are disabled in this mode..."

    # TODO: Maybe: Build these into the Compat warnings
    test_time_warn = False
    if int(isp_runtime) < 120:
        print "WARNING! If drives under test are EWP drives, recommended runtime is >=2minutes (120s)."
        test_time_warn = True
    if int(isp_ramp_time) < 60:
        print "WARNING! If drives under test are EWP drives, recommended ramptime is >=1minute (60s)."
        test_time_warn = True
    if test_time_warn is True:
        stop_test = raw_input("Press enter to continue on warnings. Press [Q] then enter to quit: ")
        if 'Q' in stop_test.upper():
            quit(0)

    isp_global = Workload(jobname='global', run_time=isp_runtime, blocksize='4K', ramp_time=isp_ramp_time,
                          bw_avg_time=1000, start_delay=1, group_report=True)

    # TODO: change this from None to a proper pass-in (right now if user uses -d it gets ignored)
    isp_drives_list = drive_assigner(None)

    def agitator_builder(drive):
        """Use this to build a list of agitators (drives not under measured workload)"""
        agitation_job = Workload(jobname='Ag_'+OS.serial_number[drive], io_target=drive,
                                 queue_depth=1, readwrite=workload_details_dict['R'])
        return agitation_job

    for wl_type in [workload_details_dict['W'], workload_details_dict['Y']]:
        for isp_drive in isp_drives_list:
            under_test_job = Workload(jobname=OS.serial_number[isp_drive], io_target=isp_drive,
                                      queue_depth=8, readwrite=wl_type, enable_write_cache=False)

            isp_workload = (isp_global, under_test_job,)

            agitators = [agitator_builder(ag_drive) for ag_drive in isp_drives_list if ag_drive != isp_drive]

            # agitator_job = Workload(jobname='agitatorSerNum', queue_depth=1, readwrite='randread', io_target='devname')
            # agitators[0].new_group(True)

            for index, ag_job in enumerate(agitators):
                if index == 0:
                    setattr(ag_job, 'new_group', True)
                isp_workload += (ag_job,)
                print ".",

            # DEBUG:
            # print isp_workload
            # print len(isp_workload)
            print ""

            isp_workload_list.append(isp_workload)
            isp_global_list.append(isp_global)

    # DEBUG:
    # print len(isp_global_list)
    # print len(isp_workload_list)

    display_workloads_list(isp_global_list, 3)

    return isp_global_list, isp_workload_list


def display_workloads_list(workloads_to_display, time_to_wait):
    """Display the workloads in any easy to read format. Should generate and format dynamically"""

    # TODO: figure out how to skip displaying items in Workload.skip_display

    col_max_length = {}
    # https://stackoverflow.com/questions/4302166/format-string-dynamically

    # DEBUG:
    # print Workload.all_io_gen_commands
    # print Workload.global_io_gen_commands

    # Calculate the widths for each column
    for param_heading in Workload.global_io_gen_commands:
        """"Cycle each heading category"""
        category_length = []

        # Determine whether it is a special case attribute or standard
        # TODO: this will AttributeError when rw is defined in the job file instead of global
        if param_heading is 'rw':
            for disp_workload in workloads_to_display:
                """cycle each value found under the heading; use this for rw"""
                category_length.append(len(getattr(disp_workload, param_heading).io_value().fio_rw_val()))
        else:
            for disp_workload in workloads_to_display:
                """cycle each value found under heading; use this for everything except special cases"""
                param_heading_length = len(param_heading)
                # convert param_value to string so numerical values get a length
                param_value_length = len(str(getattr(disp_workload, param_heading).io_value()))

                # use the longer of heading length or value length
                if param_heading_length > param_value_length:
                    category_length.append(param_heading_length)
                else:
                    category_length.append(param_value_length)
                # category_length.append(len(getattr(disp_workload, param_heading)[1]))

        col_max_length[param_heading] = max(category_length)

    # Print the WL# heading here (only thing not generated from the Workload objects)
    print "\n\n{!s:{width}}".format("WL#", width=6),

    # Print the headers here
    for display_heading in Workload.global_io_gen_commands:
        print "{!s:{width}}".format(display_heading, width=col_max_length[display_heading] + 4),

    # Print a newline so that workloads go under the headers
    print ""

    # Print the workloads here
    total_runtime = 0

    for index, workload_to_display in enumerate(workloads_to_display):
        """cycles through workloads"""
        # print the workload index
        print "{!s:{width}}".format(str(index + 1), width=6),

        # TEST:
        total_runtime += int(workload_to_display.runtime.io_value()) + int(workload_to_display.ramp_time.io_value())
        # END TEST:

        for io_generator_command in workload_to_display.wl_gen_commands:
            """cycles through workload parameters"""
            # this for loop uses io generator parameters instead of passed in headings
            # doing this means it pulls data from the same source as the workload runner
            # which means there should be less chance of mis-displaying the workload
            if io_generator_command is 'rw':
                """get the value for rw (has additional properties, there must call out property to print)"""
                wl_val_to_print = getattr(workload_to_display, io_generator_command).io_value().fio_rw_val()
            else:
                wl_val_to_print = getattr(workload_to_display, io_generator_command).io_value()

            # Use this print blanks instead of None for cleaner display (may get rid of it)
            if wl_val_to_print is None:
                wl_val_to_print = " "

            # Do the actual printing here
            print "{!s:{width}}".format(wl_val_to_print,  width=col_max_length[io_generator_command] + 4),

        # Add a newline after each workload to prevent one giant line print
        print ""

    # Calculate and display the approximate time to complete;
    # Changing WCx may knock this off by a noticeable amount when very large numbers of drives and wls are under test
    total_runtime += int(time_to_wait) * len(workloads_to_display)
    minutes, seconds = divmod(total_runtime, 60)
    hours, minutes = divmod(minutes, 60)
    days, hours = divmod(hours, 24)
    print "\nApproximate time to complete is: %sd:%sh:%sm:%ss" % (days, hours, minutes, seconds)

    # TODO: return the total runtime, and use it for a recalc based on fan loops


def drive_assigner(targets_list):
    """This function automatically finds and targets the user selected number of drives
    Auto assign goes in alphabetical order, low to high"""

    # TODO: right now eg sg10/PD10 will come before sg2/PD2 because it sorts alphabetical not numerical, fix that

    # full drive list has form [['drive1'], ['drive2'], ['drive3_lun1', 'drive3_lun2'], etc]
    full_lun_list = OS.luns_list
    partitioned_luns_list = OS.partitioned_luns
    full_drive_list = OS.drive_list

    valid_targets = [lun for lun in full_lun_list if lun not in partitioned_luns_list]

    if targets_list is None:
        # will end up here if the user didn't use -d flag

        # Notify the user of the number of non-partitioned targets
        print "Using auto-assign routine...\n There are %d valid unpartitioned targets." % \
              (len(full_lun_list) - len(partitioned_luns_list))

        while True:
            try:
                num_drives_to_auto_assign = int(raw_input("\n\nEnter the number of logical units to auto-assign: "))
                break
            except ValueError:
                print "Must be an integer value..."

        target_luns = []

        for index, target in enumerate(valid_targets):
            if index < num_drives_to_auto_assign:
                target_luns.append(target)
                print "%d: Assigned for testing: %8s %12s" % (index+1, target, OS.serial_number[target])
            else:
                break

        print "Requested %s targets. Found %s valid target logical units." % (num_drives_to_auto_assign, len(target_luns))

    else:
        # end up here if the user did used the -d flag

        # on Windows, if user provided PDx notation convert to \\.\PHYSICALDRIVEx method (req'd by fio)
        if os.name == 'nt':

            def number_find(in_string):
                """Use this function to get all numbers in a string"""
                number = int(''.join(char for char in in_string if char.isdigit()))
                return number

            drive_numbers = [number_find(single_drive) for single_drive in targets_list]

            target_luns = ['\\\\.\\PHYSICALDRIVE' + str(drive_number) for drive_number in drive_numbers]

        else:

            target_luns = targets_list

        # this will find any partitioned drives the user selected
        targeted_partitioned_luns = [lun for lun in target_luns if lun in partitioned_luns_list]

        targets_to_remove = []
        for p_target in targeted_partitioned_luns:
            print "\n***WARNING***\nDevice contains partitions: %8s %12s" % (p_target, OS.serial_number[p_target])
            while True:
                # TODO: add an overwrite all option
                    drive_remove = raw_input("Do you want to continue? (Will DESTROY ALL DATA)\n"
                                             "[Y/n] or [R] to remove drive from test: ").upper()
                    if drive_remove == 'N':
                        quit(4)
                        print "Quitting to avoid data overwrite..."
                    elif drive_remove == 'Y':
                        print "You have chosen to overwrite %s : %s. Do NOT proceed if that is a mistake!" \
                              % (p_target, OS.serial_number[p_target])
                        break
                    elif drive_remove == 'R':
                        targets_to_remove.append(p_target)
                        break
                    else:
                        print "Invalid choice.."

        target_luns = [final_drive for final_drive in target_luns if final_drive not in targets_to_remove]

        for index, target in enumerate(target_luns):
            # TODO: Use .format style used in display_workloads_list to prevent it from staggering on large numbers
            # TODO: combine this and the nearly identical one above into a single statement
            print "%d: Assigned for testing: %8s %12s" % (index+1, target, OS.serial_number[target])

    # TODO: Test this here instead of in drives from jobs; should trigger on ISP mode as well
    target_verify = raw_input("\nVerify device list. Press Enter to continue or [Q] to Quit: ")

    if 'Q' in target_verify.upper():
        print "Quitting due to keystroke..."
        quit(0)
    else:
        return target_luns

    # return target_drives


def jobs_from_drives(list_of_drives):
    """Create a list of jobs based on drives passed in. Useful if you want 1 job per drive"""
    # TODO: Determine if this really belongs here; this is building jobs from assigned drives, not assigning drives
    # build a job for each drive
    list_of_jobs = []
    for target_drive in list_of_drives:
        # list_of_jobs.append(Workload(io_target='/dev/'+target_drive, jobname=target_drive))
        new_job = Workload(jobname=OS.serial_number[target_drive])
        new_job.filename = target_drive
        list_of_jobs.append(new_job)

    # prompt user to press Enter before run starts to be sure it never wipes data
    drive_verify = raw_input("\nVerify drive list. Press Enter to continue or [Q] to Quit: ")

    # if 'Q' in drive_verify.upper():
    #     print "Quitting due to keystroke..."
    #     quit(0)
    # else:
    #     return list_of_jobs
    return list_of_jobs


def job_builder(workload_list, jobs_list):
    """Append any defined jobs to every entry in the workloads list. """

    workload_list_with_jobs = []

    for workload_global_only in workload_list:
        # add the global define as the first job entry
        workload_with_job = (workload_global_only,)
        for job in jobs_list:
            # add each job to the current workload entry
            workload_with_job += (job,)

        # create a new list of workloads that have had jobs added
        workload_list_with_jobs.append(workload_with_job)

    # This returns a tuple with (global, job1, job2, ..., jobN)
    # where each item in the tuple is an object of the Workload class
    return workload_list_with_jobs


def run_fio_and_save_results(workloads_to_run, result_location, result_table, sleep_time,
                             row_id, wl_id, read_data_to_pull, write_data_to_pull, fan_power):
    """Actually set up and run the desired workloads here"""

    # DEBUG
    # result_db = 'SummaryFile.db'
    # result_table = 'ResultTable'

    # use this to track fio errors
    fio_errors_list = []

    results_db_location, result_db = os.path.split(result_location)
    #
    # # Create the results folder if it doesn't already exist
    # if not os.path.exists(results_db_location):
    #     os.makedirs(results_db_location)
    #
    # # TODO: Get this out of here, it makes no sense to put it here.
    # # call the db creator fct to set up results storage and get the values in the table if it already exists
    # result_table, table_id, wl_id, read_data_to_pull, write_data_to_pull = \
    #     create_results_db(results_db_location, result_db, result_table)

    # print wl_id
    # raw_input()

    # initialize the row counter to 0 (id saves to database to give each row a unique id)
    # table_id = 0

    # create a workload id. Will only count workloads, not jobs
    # wl_id = 0

    # loop number is needed to track runs through each loop as wl_id will be too high if appending to old table
    loop_number = 0

    for workload_to_run in workloads_to_run:
        """cycle by workload"""

        # Increment the workload counter by 1 for each workload
        wl_id += 1

        # create the initial command line string with unchanging settings
        # TODO: make sure that direct=1 really should be here
        command_line_string = [fio, '--direct=1', '--minimal']
        output_string = ""

        # insert the OS specific fio commands
        # TODO: switch this to use the Workloads objects rather than a command line append
        if os.name == 'nt':
            command_line_string.insert(1, '--ioengine=windowsaio')
            # TODO: verify that thread=1 is still true and needed
            command_line_string.insert(2, '--thread=1')
        else:
            command_line_string.insert(1, '--ioengine=libaio')

        # need to create a list of all drive that will be targeted (regardless of the source)
        all_target_devices = []

        # create the list of iog commands and their values for db builder
        # TODO: find a more graceful way to intergrate fan_speeds (possibly similar to write_cache??)
        iog_commands = ['ID', 'WLID', 'fan_pwm']
        iog_values = [row_id, wl_id, fan_power]

        # set the write cache setting to None by default
        current_wl_wc = None

        for job_to_run in workload_to_run:
            """cycle by job (workload_to_run has form (global, job1, ..., jobX)"""

            # # DEBUG:
            # print getattr(job_to_run, 'name').io_value()
            # print job_to_run.wl_gen_commands
            # raw_input()

            row_id += 1
            iog_values[0] = row_id

            for wl_operation in job_to_run.wl_gen_commands:
                """cycle each defined fio/IOMeter command"""

                num_job_cmds_to_remove = 0

                if wl_operation is 'rw':
                    """rw has additional properties, this is a special pull for that"""
                    val_of_cmd = getattr(job_to_run, wl_operation).io_value().fio_rw_val()

                elif wl_operation is 'filename':
                    """need to know all drives that will be targeted, collect that list here"""
                    all_target_devices.append(getattr(job_to_run, wl_operation).io_value())
                    val_of_cmd = getattr(job_to_run, wl_operation).io_value()

                elif wl_operation is 'bs':  # or wl_operation is 'runtime':
                    """bs has a normalized value for better sorting, collect that here"""
                    val_of_cmd = getattr(job_to_run, wl_operation).io_value()
                    normalized_value = getattr(job_to_run, wl_operation).io_normalized()

                elif wl_operation is 'write_cache_setting':
                    """write cache is changed by 3rd party tool, not fio/IOMeter, so account for that here"""
                    current_wl_wc = getattr(job_to_run, wl_operation).io_value()
                    val_of_cmd = current_wl_wc

                else:
                    """all non-special cases go here"""
                    val_of_cmd = getattr(job_to_run, wl_operation).io_value()

                # append the command unless it is in the list of non-wlg commands
                if wl_operation not in Workload.non_wlg_commands:
                    command_line_string.append('--' + str(wl_operation) + '=' + str(val_of_cmd))

                # TODO: if the else portion is instead set to always run (ie not in an else) then the output saves
                # TODO: cont: only the settings modified by each loop.
                # TODO: cont: Check to see if a job modifies a global whether that global gets overwritten
                if getattr(job_to_run, 'name').io_value() == 'global':
                    """only define output file names using global properties as including jobs would get too long"""
                    output_string = str(output_string) + str(wl_operation) + '_' + str(val_of_cmd) + '__'
                else:
                    """use this so that non-global jobs don't duplicate in the result table"""
                    num_job_cmds_to_remove = len(job_to_run.wl_gen_commands)

                # append the active command and active value to the variables for passage to db populator
                iog_commands.append(str(wl_operation))
                iog_values.append(str(val_of_cmd))

            # # DEBUG
            # print iog_values
            # print command_line_string
            populate_results_db(results_db_location, result_db, result_table, workload_to_run, iog_commands, iog_values)

            # remove the job commands after; we want global to duplicate for each job, but NOT the jobs
            if num_job_cmds_to_remove > 0 and job_to_run.name.io_value() is not 'global':
                iog_values = iog_values[:-num_job_cmds_to_remove]
                iog_commands = iog_commands[:-num_job_cmds_to_remove]

        # take care of the calls to 3rd party utilities for cache stuff here
        if current_wl_wc is not None:
            for target_device in all_target_devices:
                OS.write_cache(target_device, current_wl_wc)

        # Strip the trailing '__' from the filename string
        if output_string[-2:] == '__':
            output_string = output_string[:-2]

        # Give fio output files the file type .txt
        output_string += '.txt'

        # The output string is finalized here
        command_line_string.append('--output=' + os.path.join(results_db_location, output_string))

        # DEBUG:
        # print command_line_string

        loop_number += 1
        print "Starting workload: %s of %s" % (loop_number, len(workloads_to_run))

        # Sleep for the defined amount of time
        if verbose_mode is True:
            print "Idling for %s seconds..." % sleep_time
        time.sleep(sleep_time)

        # This will actually run fio.
        if verbose_mode is True:
            print "Running fio with command: \n%s" % command_line_string
        p = subprocess.Popen(command_line_string)
        p.wait()

        # Once the workload completes, put its data into the table. Parse and save only returns errors
        fio_errors = parse_and_save_wlg_results(results_db_location, result_db, result_table, output_string,
                                                workload_to_run, read_data_to_pull, write_data_to_pull, wl_id)

        fio_errors_list.append(fio_errors)

    # Create the .csv file; first must get the data out of the db table
    conn = sqlite3.connect(os.path.join(results_db_location, result_db))
    cur = conn.cursor()
    with conn:
        cur.execute("SELECT * from %s" % result_table)
        column_names = [description[0] for description in cur.description]
        db_by_line = cur.fetchall()  # returns a list of tuples

    csv_file = os.path.join(os.path.split(result_location)[0], result_table) + '.csv'

    # DEBUG:
    # print str(os.path.join(os.path.split(result_location)[0], result_table) + '.csv')

    csv_saver = open(csv_file, 'w')

    # DEBUG
    # print column_names

    # write a header
    csv_saver.write(','.join(column_names))
    # write each line
    for db_line in db_by_line:

        csv_saver.write('\n')
        csv_saver.write(','.join(str(db_val) if db_val is not None else '' for db_val in db_line))

    csv_saver.close()

    # TODO: make sure this works on all fio errors; not tested on certain kinds of error
    def all_nested_lists_empty(input_list):
        """Checks nested lists for emptiness; for each element it looks for a list,
        then calls itself if the element is a list, etc. Works because 'all' returns True on empty list"""
        if isinstance(input_list, list):  # make sure it's really a list
            return all(map(all_nested_lists_empty, input_list))
        return False

    if not all_nested_lists_empty(fio_errors_list):
        print "****WARNING**** \nThere may be fio errors in results file: "
        for fio_error in fio_errors_list:
            print fio_error[0]

    print "\nAll workloads complete!"

    return row_id, wl_id


def create_results_db(result_location, db_results_file, db_results_table):
    """create the database file and table for the workloads list"""
    # TODO: determine if this would be better as a pandas table(probably not)

    def build_table(save_to_location, db_table_name, desired_data):
        """Use this to actually build the table"""

        conn = sqlite3.connect(save_to_location)
        c = conn.cursor()

        # this is vulnerable to SQL injection, but if someone is dumb enough to sabotage their own results, so be it
        # TODO: fix it eventually
        # (ID, is tacked onto the end of the string to create the first column since the loops method won't hit it
        # TODO: only add fan_pwm if fan speeds get modified
        table_maker_string = "CREATE TABLE IF NOT EXISTS %s (id, WLID, fan_pwm, " % db_table_name

        # print Workload.all_io_gen_commands

        for column_name in Workload.all_io_gen_commands:
            '''steps through every command that has been issued to create the table that is desired'''

            table_maker_string = table_maker_string + str(column_name) + ','

            if column_name is 'bs':
                table_maker_string += 'bs_normalized,'

            # TODO: Decide if this is useful, or if just using jobname=<serialnum> is better
            # if column_name is 'filename':
            #     table_maker_string += 'serial_number,'

        data_points_cols = ','.join(desired_data)

        table_maker_string += data_points_cols

        if table_maker_string[-1] is ',':
            table_maker_string = table_maker_string[:-1]

        table_maker_string += ')'

        # DEBUG
        # print table_maker_string
        c.execute(table_maker_string)

        conn.commit()
        conn.close()

    # TODO: Allow this to be a user pass-in
    # The list of data to pull out of the results (create the headers with it here
    data_points_to_pull = ['bw', 'iops', 'mean_latency', '50_latency', '90_latency',
                           '95_latency', '99_latency', '99.9_latency', '99.95_latency', '99.99_latency']

    # create a read and write column for each data point that the user asks for
    read_data_points_to_pull = ['"read_' + data_point_to_pull + '"' for data_point_to_pull in data_points_to_pull]
    write_data_points_to_pull = ['"write_' + data_point_to_pull + '"' for data_point_to_pull in data_points_to_pull]

    # Combine the read and write data points
    desired_data_points = read_data_points_to_pull + write_data_points_to_pull

    # don't just dive into the .db if it doesn't exist
    if os.path.isfile(os.path.join(result_location, db_results_file)):
        print "There is already a results database file here, no new file created..."

        # The execute statement should return nothing if the table doesn't exist, return the name if it does
        conn = sqlite3.connect(os.path.join(result_location, db_results_file))
        c = conn.cursor()
        c.execute("SELECT name FROM sqlite_master WHERE type='table' AND name=?", (db_results_table,))
        extant_table = c.fetchone()

        # check if the table already exists
        if extant_table:
            print "\n\nTable %s already exists..." % extant_table

            # TODO: Fix the cases this warning warns about, or at least make the script detect it
            print "\n****WARNING**** \n\nThe script can attempt to append the new data to the existing table, " \
                  "but this will work IF AND ONLY IF the new table has the exact same columns as the old." \
                  " eg: You may not add mixed workloads to a table that doesn't already contain them, " \
                  "or write cache changes if the last run didn't alter cache, etc. This will be updated later." \
                  "\n\nAn invalid choice WILL CRASH the script when the violating workload is reached.\n\n" \
                  "You may choose to:" \
                  "\n[N]: Create new table in same .db file. The .csv will also use this name." \
                  "\n[A]: Append to the exisiting table. Please heed the warning above." \
                  "\n[D]: Delete and overwrite the existing table." \
                  "\n[Q]: Quit."

            while True:
                table_choice = raw_input("Select a letter then press Enter: ")

                if table_choice.upper() == 'N':
                    # TODO: This will break in saving results, fix the script by returning the new table location
                    table_name = raw_input("Enter a new table name: ")
                    max_result_id = 0
                    max_wl_id = 0

                    build_table(os.path.join(result_location, db_results_file), table_name, desired_data_points)

                    break

                elif table_choice.upper() == 'A':
                    table_name = db_results_table

                    c.execute("SELECT MAX(id) FROM %s" % db_results_table)
                    max_result_id = c.fetchone()
                    # c.fetchone returns a tuple here, need an int
                    max_result_id = int(max_result_id[0])

                    c.execute("SELECT MAX(WLID) FROM %s" % db_results_table)
                    max_wl_id = c.fetchone()
                    # c.fetchone returns a tuple here, need an int
                    max_wl_id = int(max_wl_id[0])

                    break

                elif table_choice.upper() == 'D':
                    table_name = db_results_table
                    max_result_id = 0
                    max_wl_id = 0

                    # Drop the old table
                    c.execute("DROP TABLE IF EXISTS %s" % table_name)
                    # Rebuild it with new parameters
                    build_table(os.path.join(result_location, db_results_file), table_name, desired_data_points)

                    break

                elif table_choice.upper() == 'Q':
                    print "Quitting due to user choice..."
                    quit(0)

                else:
                    print "Invalid choice..."

        else:  # if it ends up here, should create a new table in the same file
            print "\nDB file exists, but table does not, creating new table %s" % db_results_table
            table_name = db_results_table
            max_result_id = 0
            max_wl_id = 0
            build_table(os.path.join(result_location, db_results_file), table_name, desired_data_points)

    else:  # it gets to here if the file doesn't exist already

        build_table(os.path.join(result_location, db_results_file), db_results_table, desired_data_points)

        table_name = db_results_table
        max_result_id = 0
        max_wl_id = 0

    return table_name, max_result_id, max_wl_id, read_data_points_to_pull, write_data_points_to_pull


def populate_results_db(result_loc, db_results_file, db_results_table, active_workload, columns_list, values_list):
    """add the the workloads and jobs to the table after each workload completes. Data is added in other fct (for now)
    The passed in columns and values here should be a single workload; this does no looping"""

    # TODO: this whole fct is going to do weird things if something is defined more than once.

    # if os.path.isfile(os.path.join(result_loc, db_results_file)):
    #     pass

    # TODO: reindent this under the if statement when you figure out why the if statement doesn't work
    conn = sqlite3.connect(os.path.join(result_loc, db_results_file))
    c = conn.cursor()

    inserter_string = 'INSERT INTO %s (' % db_results_table

    # If blocksize is listed, need to also add the normalized value (plus appropriate header)
    # for job in active_workload:
    #     '''steps through all the jobs in the active workload to look for bs'''
    #     # TODO: this fails on any jobs without their own blocksize
    #     pass

    # if 'bs' in columns_list:
    #     columns_list.append('bs_normalized')
    #     values_list.append(job.bs.io_normalized())

    # join together the columns list, and append the closing ')'
    columns = ', '.join(columns_list)
    columns += ')'

    # This sets the value of None elements to 'null' to match SQL syntax
    values_list = [val if val != 'None' else None for val in values_list]
    # join together the values list placeholder, and append the closing ')'
    values = ['?'] * len(values_list)
    values = ', '.join(values)
    values += ')'

    # Finalized the insertion string
    inserter_string = inserter_string + columns + ' VALUES (' + values

    # Run the command
    c.execute(inserter_string, tuple(values_list))

    conn.commit()
    conn.close()


def parse_and_save_wlg_results(result_location, db_file, table_name, fio_result_file,
                               active_wl, rd_datapoints, wrt_datapoints, wl_number):
    """take the fio output and parse it out into the needed format to add it to the database
    Will return the filename of any errors encountered (1 per file name)"""
    # TODO: this should maybe combine with populate_results_db fct; they're very similar

    with open(os.path.join(result_location, fio_result_file), 'r') as wl_results:
        wl_result_line = wl_results.readlines()
    wl_results.close()

    conn = sqlite3.connect(os.path.join(result_location, db_file))
    c = conn.cursor()

    fio_parse_errors = []

    for job_line in wl_result_line:
        if not job_line.startswith('3;'):
            fio_parse_errors.append(str(fio_result_file))
        else:
            # split the fio minimal ouptut so that it can be called by name instead of index
            single_job_result = FioMinimalOut(job_line.split(';'))

            job_name = single_job_result.jobname()

            # each loop reset the db string that will eventually put the data in the table
            # TODO: fix with this:
            #   https://www.daniweb.com/programming/software-development/threads/377210/python-sqlite-update-with-multiple-parameters#
            db_insertion_string = 'UPDATE %s SET' % table_name

            # Get the results based on the desired outputs list
            # request_data will = all of the desired columns to be filled
            # TODO: make this work in cases where the job redefines the read/write setting
            # TODO: cont: I think the [0] in active_wl[0] is looking to the global in workloads + jobs tuple
            # TODO: the try:except will allow cases where there is no global defined to work, but it pulls both
            # TODO: use the value in rw col to determine what to pull
            try:
                if active_wl[0].rw.io_value().is_writes() is True and active_wl[0].rw.io_value().is_mixed() is True:
                    request_data = rd_datapoints + wrt_datapoints

                elif active_wl[0].rw.io_value().is_writes() is True and active_wl[0].rw.io_value().is_mixed() is False:
                    request_data = wrt_datapoints

                elif active_wl[0].rw.io_value().is_writes() is False and active_wl[0].rw.io_value().is_mixed() is False:
                    request_data = rd_datapoints
                else:
                    request_data = rd_datapoints + wrt_datapoints
            except AttributeError:
                request_data = rd_datapoints + wrt_datapoints

            for data_request in request_data:
                """use this to get the proper FioMinimalOut call based database table headers"""
                # The .split('_') is splitting based on the table headers, assuming the format <read/write>_<bw/iops>
                if 'bw' in data_request:
                    data_value = single_job_result.bw(data_request.split('_')[0])
                elif 'iops' in data_request:
                    data_value = single_job_result.iops(data_request.split('_')[0])
                elif 'latency' in data_request:
                    # latency needs 2 values; both the r/w and the percentage;
                    # the class uses ints but numbers are read from the db table columns as strings;
                    # if the conversion fails it pulls the mean
                    # TODO: maybe make it report PctErr instead of mean...
                    try:
                        data_value = single_job_result.latency(data_request.split('_')[0],
                                                               float(data_request.split('_')[1]))
                    except ValueError:
                        data_value = single_job_result.latency(data_request.split('_')[0],
                                                               (data_request.split('_')[1]))
                else:
                    data_value = None

                # insert all the SET column = value statements to the update line here
                # TODO: do it 'proper' instead of string substitution (but if someone nukes their own table...)
                db_insertion_string = db_insertion_string + ' ' + str(data_request) + '=' + str(data_value) + ','

            # trim the trailing comma
            if db_insertion_string[-1] is ',':
                db_insertion_string = db_insertion_string[:-1]

            # only update the job being parsed for the current workload
            db_insertion_string = db_insertion_string + ' WHERE WLID=%s AND name="%s";' % (wl_number, job_name)

            # DEBUG:
            # print db_insertion_string

            c.execute(db_insertion_string)

            conn.commit()

    # Get any data requested; there shouldn't be much time penalty for looking at unnecessary columns
    all_requested_data = rd_datapoints + wrt_datapoints
    # Calculate and insert the average values and set name="Average"
    for result_data in all_requested_data:
        """step through column by column getting and calculating the average for each WL"""
        get_data_string = "SELECT %s FROM %s WHERE WLID=%s" % (result_data, table_name, wl_number)

        # pull all values in the column, and save to list
        c.execute(get_data_string)
        tuple_to_avg = c.fetchall()

        # c.fetchall returns a list of 1 element tuples; turn that into a list and ignore entries that have None value
        list_to_avg = [data_val[0] for data_val in tuple_to_avg if data_val[0] is not None]

        # This will make it skip cases(and assign NULL) where all values are Null/None and avoid a x/0 error
        if len(list_to_avg) == 0:
            avg_val = 'null'
        else:
            avg_val = sum(list_to_avg)/len(list_to_avg)

        # create the insertion string
        # TODO: yes, this one can be SQL injected too. Fix if possible
        avg_insertion_string = 'UPDATE %s SET %s=%s WHERE WLID=%s AND name is null' % \
                               (table_name, result_data, avg_val, wl_number)

        c.execute(avg_insertion_string)

        conn.commit()

    # update the col 'name' = "Average" on the global row (since it has no fio results, it's saved as avg of all wls)
    c.execute('UPDATE %s SET name="Average" WHERE WLID=%s AND name is null' % (table_name, wl_number))

    conn.commit()

    conn.close()

    return fio_parse_errors  # should be list of empty lists if there are no parser errors


def workload_list_saver(workloads_as_objects, filename):
    """Use this to save the currently generated workload list as a python pickle object to disk
    Will prompt user for the name. Return True if it worked."""
    # TODO: decide if it's better to import every time save is called, or always
    # Since save likely only gets called once, and likely not on every run, it probably should stay here...
    try:
        import cPickle as pickle
    except ImportError:
        import pickle

    with open(filename, 'wb') as output:
        pickle.dump(workloads_as_objects, output, -1)


def workload_list_loader(filename):
    """Load a workload list that has been saved to disk. This must load the list then rebuild the object.
    If a fio attribute exists in the save file but not in the version of the script being loaded, it will be dropped"""
    # TODO: decide if it's better to import every time save is called, or always

    try:
        import cPickle as pickle
    except ImportError:
        import pickle
    # try:
    #     import dill as pickle
    with open(filename, 'rb') as infile:
        loaded_wl_list = pickle.load(infile)

    # This gets all the possible attributes of the workload class in the current version of the script
    wl_class_attrs = [attr for attr in dir(Workload) if not callable(getattr(Workload, attr))
                      and not attr.startswith("__")]
    if 'rw' in wl_class_attrs:
        wl_class_attrs.remove('rw')
        wl_class_attrs.insert(0, 'rw')

    rebuilt_wl_list = []

    for index, loaded_wl in enumerate(loaded_wl_list):
        """This loop gets the loaded attribute settings, then creates a new object by setting it's attributes properly.
        This is required because the class variables cannot be saved by pickle, and they must rebuild based on loaded 
        data"""
        # print "Workload: %s of %s loaded" % (index+1, len(loaded_wl_list))
        # rebuilt_wl_list.append(Workload(jobname='global'))
        rebuilt_wl_list.append(Workload('global'))
        for wl_attr in wl_class_attrs:

            if wl_attr == 'rw':
                current_attr_val = getattr(loaded_wl, wl_attr).io_value()
                setattr(rebuilt_wl_list[index], wl_attr, current_attr_val)

            else:
                try:
                    # only fio commands are attributes; there are class variables are manipulated by the fio methods
                    # This is a viable way to catch them
                    current_attr_val = getattr(loaded_wl, wl_attr).io_value()
                    setattr(rebuilt_wl_list[index], wl_attr, current_attr_val)

                except AttributeError:
                    # class variables that aren't fio attributes fall out here as do unsupported attributes
                    pass

    return rebuilt_wl_list


def main():
    """Initialize the script, parse the command line options, and run the wlg"""

    def edit_workloads_list(workload_list, wait_time):
        """Use this to allow user to decide what to do with the current workload list.
        Options include add, delete, save, run, or quit"""

        prompt_active = True
        new_list_of_wls = list_of_workloads
        while prompt_active is True:
            display_workloads_list(new_list_of_wls, wait_time)
            print "\n\nWhat would you like to do with the current workload list?"
            print "[C]: Confirm the workload list and start drive I/O operations.\n" \
                  "[A]: Add one or more workloads. Can insert or append.\n" \
                  "[D]: Delete a workload.\n" \
                  "[S]: Save the workloads list to a file.\n" \
                  "[Q]: Quit this script."

            user_choice = raw_input("Input a key: ").upper()

            if user_choice == 'C':
                # return the workload list as it currently exists
                prompt_active = False
                return new_list_of_wls
                # run_fio_and_save_results(workload_list, result_loc, result_db_table, wait_time)

            elif user_choice == 'A':
                # calls the workload generators again
                new_wl_defines, new_wls_to_build, new_wc_options = \
                    custom_workload_prompts(args.advanced_options, args.smr_mode)
                new_list_of_wls += generate_workloads_list(new_wl_defines, new_wls_to_build,
                                                           new_wc_options, args.run_time, args.ramp_time)
            elif user_choice == 'D':
                while True:
                    try:
                        wl_to_delete = int(raw_input("Enter the number of the workload to delete, "
                                                     "blank goes back: ")) - 1
                        del new_list_of_wls[wl_to_delete]
                        break
                    except ValueError:
                        print "Must be an integer value."
                    except IndexError:
                        print "No workload with that number exists."

            elif user_choice == 'S':
                print "Will save to the current results directory: %s" % os.path.abspath(results_db_path)
                wl_list_savefile = raw_input('Enter a filename to save as: ')
                if wl_list_savefile[-3:].lower() != '.pkl':
                    wl_list_savefile += '.pkl'

                wl_save_name = os.path.join(results_db_path, wl_list_savefile)

                # Create the results folder if it doesn't already exist
                if not os.path.exists(results_db_path):
                    os.makedirs(results_db_path)

                # save it if no file has that name, otherwise don't (due to current structure, this returns to the menu)
                if not os.path.isfile(wl_save_name):
                    workload_list_saver(workload_list, wl_save_name)
                    print "Workload saved to: %s" % str(os.path.abspath(wl_save_name))
                else:
                    print "\n\n!!!!NOT SAVED!!!!. \n\nWorkload file %s already exists, choose a new name." % \
                          str(os.path.abspath(wl_save_name))
                time.sleep(1)

            elif user_choice == 'Q':
                print "Quitting..."
                quit(0)

            else:
                print "\nInvalid selection. Try again..."
                time.sleep(1)

    parser = argparse.ArgumentParser(description="Create, run, and parse a series of fio scripts. Executing the "
                                                 "script will launch a series of prompts to select workload options, "
                                                 "then create and run list of every possible workload combination. "
                                                 "The results are saved to a database table and printed to a .csv file")
    parser.add_argument("-t", "--runtime", dest="run_time", default=180,
                        help="Set the runtime of each individual test. Default units are seconds. "
                             "Default is %(default)ss.")
    parser.add_argument("-r", "--ramptime", dest="ramp_time", default=10,
                        help="Set a time to run workload without recording results in seconds. "
                             "Default time is %(default)s seconds.")
    parser.add_argument("-w", "--waittime", dest="time_to_sleep", default=5,
                        help="Set a time to idle between each workload. Default is %(default)s seconds.")
    parser.add_argument("-d", "--device", nargs='+', dest="target_devices",
                        help="Define one or more drives to target. Must use -d only once. "
                             "Ie Use '-d /dev/sdx /dev/sdy' NOT '-d /dev/sdx -d /dev/sdy' ")
    parser.add_argument("-i", "--inputfile", dest="load_from_file",
                        help="Use this to load a previous workload. -t, -r options will only apply to workloads added "
                             "to the list in the current session.")
    parser.add_argument("-o", "--output", dest="outpath", default=os.path.join('Results', 'LatencyResults.db'),
                        help="Location to save results to. May be an existing database, existing directory, or new "
                             "file/directory. To create a new file with a specific name, append '.db' to the input "
                             "to this option, otherwise it will save to 'OUTPATH/LatencyResults.db'.")
    parser.add_argument("-n", "--tablename", dest="table_name", default="ResultTable",
                        help="Script parses results to a database file and a csv file. This will set the name of the "
                             "table within the database and the name of the csv file.")
    parser.add_argument("-f", "--fancommand", nargs='+', dest="fan_command", default=None,
                        help="Input the command used to control fan speed. Use $D(decimal) or $H(hex) to specify the"
                             " field that represents the fan speed. Commands with spaces must be enclosed in quotation"
                             " marks. "
                             "Eg:\n -f 'ipmitool raw 0x2E 0x05  0xFD 0x19 0x00  00  0x00 $H'. "
                             "If the command must be issued per fan (ie one command to fan 0, one to fan 1, etc) enter "
                             "the command multiple times, eg:\n"
                             " -f 'ipmitool raw 0x2E 0x05  0xFD 0x19 0x00 00 0x00 $H' "
                             "'ipmitool raw 0x2E 0x05  0xFD 0x19 0x00 01 0x00 $H'")
    parser.add_argument("-s", "--fanspeeds", nargs='+', dest="fan_speeds", default=None,
                        help="Provide fan speeds to run, separated by space. Number format (hex vs. dec) must match the"
                             " format provided in -f, --fancommand.")
    parser.add_argument("-A", "--AdvancedOptions", dest="advanced_options", action="store_true",
                        help="Enable advanced workload options. (NOT currently implemented)")
    # parser.add_argument("-Q", "--QuietMode", dest="fio_suppress", action="store_true",
    #                     help="Suppress all fio ETA and other outputs. (NOT currently implemented)")
    parser.add_argument("-Z", "--ZoneBlockDevice", dest="smr_mode", action="store_true",
                        help="Set this flag to run SMR drives. Note this setting applies to ALL drives under test.")
    parser.add_argument("-I", "--ISPmode", dest="isp_test", action="store_true",
                        help="Put the script into ISP (In System Performance) test mode. This mode is used to test "
                             "the throughput under various fan loads. If this option is used without defining -f,"
                             " --fancommand and -s, --fanspeeds the script will halt after each loop and request that "
                             "the user manually set the fans. Default runtime is changed to 30s.")
    parser.add_argument("-V", "--Verbose", dest="verbose_mode", action="store_true",
                        help="Display detailed info while running.")
    parser.add_argument("--version", action="version", version="%(prog)s {version}".format(version=__version__))

    # TODO: Implement the commented out options
    # TODO: Add -D, --ListDevices to list the drives auto select will choose, then quit.
    # TODO: Add -S, --Stonewall (maybe name/letter change) to add the fio stonewall option and run 1 at a time
    # TODO: Add -L, --LogSave to allow saving of bw, iops, and lat logs (maybe use 1 flag each?)(might have mem issues)
    # TODO: Add - , --temperaturecheck that takes an interval in sec to get drive temperature. Default to not check it
    # TODO: Add -I, --ISPtest to put it into ISP test mode. Use 'ISP_example.fio' for how to set that up.
    args = parser.parse_args()

    # Save verbosity and quiet as globals to avoid pass-in, since they should never change
    global verbose_mode
    verbose_mode = args.verbose_mode

    global OS
    OS = SystemCommands(os.name)

    # Check for system compatibility
    compat_check(os.name)

    # Check to see if the user has given a directory or a file name and act as appropriate
    if os.path.isfile(args.outpath):  # if given an existing file, append to it
        db_location = args.outpath
    elif os.path.exists(args.outpath):  # if given an extant folder, save to the folder with the default db filename
        db_location = os.path.join(args.outpath, "LatencyResults.db")
    elif args.outpath.endswith('.db'):  # if given anything that ends with .db assume it's a file, not folder
        db_location = args.outpath
    else:  # if it doesn't exist and doesn't end in .db, assume the user wants to create a folder
        db_location = os.path.join(args.outpath, 'LatencyResults.db')

    # check to see of the user has chosen to load a saved workload list,
    # and call the loader and skip the 1st set of generator steps if so
    if args.load_from_file:
        print "Loading from file: %s" % os.path.abspath(args.load_from_file)
        list_of_workloads = workload_list_loader(args.load_from_file)

        # give the user the option to edit their workload list (also where the display function is called
        final_list_of_workloads = edit_workloads_list(list_of_workloads, args.time_to_sleep)

        # TODO: Everything from here to the elif is a copy paste of everything past generate_workloads_list in the else

        # Determine if the user has used -d to add device targets, and if not pass in None to launch auto-assign routine
        if args.target_devices:
            # print "Drives given: %s" % args.target_devices
            drive_list = drive_assigner(args.target_devices)
            drives_as_jobs = jobs_from_drives(drive_list)
        else:
            drive_list = drive_assigner(None)
            drives_as_jobs = jobs_from_drives(drive_list)

        # for now this builds a unique job for each device. Once we allow custom jobs this might change
        # TODO: sort this out for custom jobs and ISP mode
        workloads_plus_devices = job_builder(final_list_of_workloads, drives_as_jobs)

    elif args.isp_test is True:
        # TODO: pull fan_command and fan_speed out of this; see line 2196 for why
        list_of_workloads, workloads_plus_devices = isp_mode(args.fan_command, args.fan_speeds,
                                                             args.run_time, args.ramp_time)

        # TODO: pull the create db fct out of run_fio_and_save results. done! test w regular mode
        # TODO: Loop run_and_save once per fan speed
        # TODO: Figure out how to add the fan speeds to the table as a column
        # TODO: Figure out where the hell I put that reordering of columns (and kick myself for doing that)
        # TODO: Keep advanced user flexibility in mind when modifying all this
        # TODO: see 2196; loop fan speeds and add fan speed column any time user gives them, not just in ISP mode
        # DEBUG:
        # quit(0)

    else:
        # Call the custom prompts for the first loop (all subsequent are in edit_workloads_list fct
        workload_defines, workloads_to_build_, write_cache_options = \
            custom_workload_prompts(args.advanced_options, args.smr_mode)

        # Generate the list based on what was selected by the user in 1st custom prompts section
        list_of_workloads = generate_workloads_list(workload_defines, workloads_to_build_, write_cache_options,
                                                    args.run_time, args.ramp_time)

        # give the user the option to edit their workload list (also where the display function is called
        final_list_of_workloads = edit_workloads_list(list_of_workloads, args.time_to_sleep)

        # Determine if the user has used -d to add device targets, and if not pass in None to launch auto-assign routine
        if args.target_devices:
            # print "Drives given: %s" % args.target_devices
            drive_list = drive_assigner(args.target_devices)
            drives_as_jobs = jobs_from_drives(drive_list)
        else:
            drive_list = drive_assigner(None)
            drives_as_jobs = jobs_from_drives(drive_list)

        # for now this builds a unique job for each device. Once we allow custom jobs this might change
        # TODO: sort this out for custom jobs and ISP mode
        workloads_plus_devices = job_builder(final_list_of_workloads, drives_as_jobs)

    # separate the filename from the path so that the user can be told each
    # out_dir, db_name = os.path.split(db_location)

    results_db_path, result_db = os.path.split(db_location)

    # Create the results folder if it doesn't already exist
    if not os.path.exists(results_db_path):
        os.makedirs(results_db_path)

    # TODO: Make sure this works outside the run_and_save fct
    # call the db creator fct to set up results storage and get the values in the table if it already exists
    result_table, table_row_id, wl_id, read_data_to_pull, write_data_to_pull = \
        create_results_db(results_db_path, result_db, args.table_name)

    print "\nWill save all files to the location: \n%s" % os.path.abspath(results_db_path)

    # TODO: loop through fan speeds in ALL modes if the user gives a fan_command and fan_speed list
    # actually runs it and saves it
    if args.fan_command is not None and args.fan_speeds is not None:
        # TODO: maybe put the create_results_db here to avoid creating a pwm column when it isn't needed

        # TODO: recalc the total runtime, as it doesn't account for fan loops (see ~line 1277)

        # TODO: id, WLID reset every fan loop, fix it so that the correct isd, WID are passed in on each loop

        for fan_speed_index, fan_speed in enumerate(args.fan_speeds):
            print "Running fan speed setting %s of %s" % (fan_speed_index, len(args.fan_speeds))
            fan_speed_int = None
            for fan_command in args.fan_command:
                """this is currently written on the assumption that each command controls 1 fan"""
                if '$h' in fan_command.lower():
                    # use hex logic here
                    # TODO: look for 0x## or ##h to check hex indicators; for now this just runs what the user gave it

                    part_fan_command = fan_command.replace('$H', fan_speed)
                    final_fan_command = part_fan_command.replace('$h', fan_speed)

                    # convert hex fan speed value to decimal for saving results and plotting
                    fan_speed_int = int(fan_speed.strip('hH'), 16)

                    print "Setting fan(s) to: %s (%s d)" % (fan_speed, fan_speed_int)

                    # if verbose_mode is True:
                    #     print "Setting fan(s) to: %s (%s d)" % (fan_speed, fan_speed_int)

                elif '$d' in fan_command.lower():
                    # use decimal logic here
                    part_fan_command = fan_command.replace('$D', fan_speed)
                    final_fan_command = part_fan_command.replace('$d', fan_speed)
                    fan_speed_int = int(fan_speed)

                    print "Setting fan(s) to: %s" % fan_speed

                    # if verbose_mode is True:
                    #     print "Setting fan(s) to: %s" % fan_speed

                else:
                    print "Could not find '$H' or '$D' in fan command input:\n %s \n" \
                          "This value indicates the field for fan speed. " \
                          "Please review the command format given. Fan may not be set properly" % fan_command
                    final_fan_command = fan_command

                # Issue the fan change command, and wait for return status
                if verbose_mode is True:
                    print "Setting fans using command: \n%s" % final_fan_command

                # p = subprocess.Popen(final_fan_command)
                # p.wait()
                subprocess.call(final_fan_command.split())
                # os.system(final_fan_command)

            # Allow fans time to ramp to new setting
            # TODO: ??Add yet another user option??
            if verbose_mode is True:
                print "Waiting 5s to allow fans time to ramp..."
            time.sleep(5)

            table_row_id, wl_id = run_fio_and_save_results(workloads_plus_devices, db_location, result_table, float(args.time_to_sleep),
                                     table_row_id, wl_id, read_data_to_pull, write_data_to_pull, fan_speed_int)

    elif args.fan_command is None and args.fan_speeds is not None:
        # TODO: put a condition where it waits for user to set fan speed manually here, then continue
        for fan_speed_index, fan_speed in enumerate(args.fan_speeds):
            print "Running fan speed %s of %s" % (fan_speed_index, len(args.fan_speeds))

            if fan_speed.startswith('0x') or fan_speed.lower().endswith('h'):
                fan_speed_int = int(fan_speed.strip('hH'), 16)

                print "Fan speed should be set to %s." \
                      "\nPlease set the fans to the desired value, then press enter to continue " % fan_speed_int
                # no input saved, just forces a wait for the speed to be set
                raw_input()
            else:
                fan_speed_int = int(fan_speed)

                print "Fan speed should be set to %s." \
                      "\nPlease set the fans to the desired value, then press enter to continue " % fan_speed_int
                # no input saved, just forces a wait for the speed to be set
                raw_input()

            table_row_id, wl_id = run_fio_and_save_results(workloads_plus_devices, db_location, result_table,
                                                           float(args.time_to_sleep),
                                                           table_row_id, wl_id, read_data_to_pull, write_data_to_pull,
                                                           fan_speed_int)

    else:
        table_row_id, wl_id = run_fio_and_save_results(workloads_plus_devices, db_location, result_table, float(args.time_to_sleep),
                                 table_row_id, wl_id, read_data_to_pull, write_data_to_pull, args.fan_speeds)

    print "\nFor plots, target the Graphing script to the database file:\n%s\n\n" % os.path.abspath(db_location)


if __name__ == "__main__":
    main()


"""Everything below here is script testing related"""

# print listofdisplaywl[1].all_io_gen_commands
# print listofdisplaywl[-1].all_io_gen_commands
#
# final_param_list = []
# for param_item in listofdisplaywl[-1].all_io_gen_commands:
#     if param_item not in final_param_list:
#         final_param_list.append(param_item)
#
# print final_param_list

# print listofdisplaywl[1].wl_gen_commands
# print listofdisplaywl[-1].wl_gen_commands
# print listofdisplaywl[-1].write_cache_setting.value
# print listofdisplaywl[-2].write_cache_setting.value
# print "\n\nAll io_gen_commands:"
# print Workload.all_io_gen_commands

# TODO: the below looks to be a good way to turn it into a CSV
'''
print "Databse test print:"
conn = sqlite3.connect('Results/SummaryFile.db')
cur = conn.cursor()
with conn:
    cur.execute("SELECT * from ResultTable")
    print cur.fetchall() 
'''
# TODO: this is how to find every callable attr in a class -- use it in the load fct
# example = Example()
# members = [attr for attr in dir(example) if not callable(getattr(example, attr)) and not attr.startswith("__")]
# print members
# print dir(Workload)
