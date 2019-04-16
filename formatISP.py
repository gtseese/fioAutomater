# Take the results output of an ISP test and put it into an Excel file with formatting

# TODO: https://www.dataquest.io/blog/python-pandas-databases
# https://xlsxwriter.readthedocs.io/working_with_pandas.html

"""
Take the results of the fioAutomater.py test and convert them to an excel sheet in the format used for ISP results
reporting.
Created by George Seese.
"""

import sqlite3
import xlsxwriter
import os

# TODO: it writes format when workbook.close is issued, therefore if format is changed all cells that use it change


def column_letter(col_num, letter_to_return=''):
    """Use this to generate a decoder that takes the python/xlsxwriter (row_int, col_int) method and translate to
    Excel style (A1, B1, A2, B2, etc) naming. This translates the col_int to a column letter"""

    # create a list of all letters, plus a blank as the first element
    # TODO: speed is ~ doubled if this is declared outside the fct
    letter_lookup = [chr(letter) for letter in xrange(ord('a'), ord('a') + 26)]
    letter_lookup.insert(0, '')

    # calculate the letter to pull out of letter lookup for the first letter
    letter_index = (col_num - 1) % 26 + 1

    # anything beyond the first letter will be stored and passed in to the function recursively
    pass_in = (col_num - 1) / 26

    letter_to_return = letter_lookup[letter_index] + letter_to_return

    if pass_in > 0:
        # recurse until there is no more pass-in value; when it is 0 there are no more column letters to add
        return column_letter(pass_in, letter_to_return)
    else:
        return letter_to_return.upper()  # by calling upper here it is only called once on the final loop


def choose_table(db_file):
    """use this function to select and choose which table in db to pull data from.
    If only one table exists, choose it by default"""

    if os.path.isfile(db_file):
        con = sqlite3.connect(db_file)
        cursor = con.cursor()
        cursor.execute("SELECT name FROM sqlite_master WHERE type='table';")
    else:
        print "\nNo file at:\n\n%s\n\nPlease check the file path and try again." % db_file
        quit(1)

    # this will return a list of 1-length tuples; anything that wants to access these tuples must target element[0]
    db_tables = cursor.fetchall()

    if len(db_tables) == 0:
        print "\nNo table found. Please check the specified database file."
        quit(1)
    elif len(db_tables) == 1:
        print "Using table with name %s" % db_tables[0]
        table_choice = db_tables[0]
        return table_choice[0]
    else:
        print "Found multiple tables. Type the number of the one you'd like to use to generate an xlsx file:"

        for table_index, table in enumerate(db_tables):
            print "{:4}: {!s}".format(table_index, table[0])

        while True:
            try:
                table_choice = raw_input("Enter table number: ")
                if 'Q' in table_choice or 'q' in table_choice:
                    quit(0)
                return db_tables[int(table_choice)][0]
            except ValueError:
                print "Must be integer value."
            except IndexError:
                print "Invalid choice. Please choose a listed table."


def get_data(db, table_name):
    """Pull the needed data out of the .db file"""

    con = sqlite3.connect(db)
    cursor = con.cursor()

    # TODO: consider adding ORDER BY fan_pwm to this
    cursor.execute("SELECT DISTINCT fan_pwm FROM %s; " % table_name)

    # fetchall returns list of length 1 tuple, convert to list of strings
    fan_speeds = [fan_pwm[0] for fan_pwm in cursor.fetchall()]

    # fan_speeds = cursor.fetchall()

    # can't figure out how to make this behave in the cursor statement so just pass it in
    ag_literal = r'%Ag%'

    cursor.execute("SELECT DISTINCT name FROM %s WHERE name NOT LIKE 'Average' AND name NOT LIKE '%s'; " %
                   (table_name, ag_literal))

    dev_names = [dev[0] for dev in cursor.fetchall()]
    # dev_names = cursor.fetchall()

    print fan_speeds
    print dev_names

    for fan_speed in fan_speeds:
        for dev_name in dev_names:

            # sqlite must have same type, use this to handle both 'baseline' and ints (ie 50)
            if isinstance(fan_speed, (int, long)):
                cursor.execute("SELECT write_bw, write_iops FROM %s WHERE fan_pwm = %d AND name = '%s';" %
                               (table_name, fan_speed, dev_name))
            else:
                cursor.execute("SELECT write_bw, write_iops FROM %s WHERE fan_pwm = '%s' AND name = '%s';" %
                               (table_name, fan_speed, dev_name))

            print cursor.fetchall()

            # TODO: Write it to Excel. This gets the correct data; form is [(randbw, randiops, seqbw, seqiops),]

    write_data = ''

    return dev_names, fan_speeds


def layout_sheet(devices, fan_values, xlsx_file_name):
    """create the table/sheet layout"""

    print "Create layout"

    workbook = xlsxwriter.Workbook(xlsx_file_name)
    worksheet = workbook.add_worksheet('FormattedResults')

    # Set the header format for "Drive Serial Number": Bold, Light gray background, thick border left
    header_format = {'left':   workbook.add_format({'bold': True, 'bg_color': '#e7e6e6', 'left': 2, 'right': 1}),
                     'center': workbook.add_format({'bold': True, 'bg_color': '#e7e6e6', 'center_across': True}),
                     'right':  workbook.add_format({'bold': True, 'bg_color': '#e7e6e6', 'left': 1, 'right': 2})
                     }

    # row and column will always equal the top left-most cell of the header
    row = 2
    col = 1
    worksheet.write(row, col, 'Drive Serial Number', header_format['left'])

    # write the device names downwards; add thick left border, standard right border
    new_row = row + 1
    for device in devices:
        worksheet.write(new_row, col, device, workbook.add_format({'left': 2, 'right': 1}))
        new_row += 1

    last_data_row = new_row

    # write the fan speeds left to right using defined header format
    new_col = col + 1
    for fan_value in fan_values:
        worksheet.write(row, new_col, fan_value, header_format['center'])
        new_col += 1

    last_data_col = new_col

    # set format for Min, Max, Average at bottom of Serial Numbers
    min_max_avg_format = {'Min': workbook.add_format({'bold': True, 'left': 2, 'right': 1, 'top': 1}),
                          'Max': workbook.add_format({'bold': True, 'left': 2, 'right': 1}),
                          'Average': workbook.add_format({'bold': True, 'left': 2, 'right': 1, 'bottom': 2}),
                          }

    # Add the 3 fan speed summary rows to the bottom of the table
    for stat in ['Min', 'Max', 'Average']:
        # write Min, Max, Average at bottom of Serial Numbers with appropriate borders
        worksheet.write(new_row, col, stat, min_max_avg_format[stat])
        # De-bold for the the numerical results (ie non-title cells)
        min_max_avg_format[stat].set_bold(False)
        min_max_avg_format[stat].set_right(0)
        min_max_avg_format[stat].set_left(0)

        for all_col in range(col+1, new_col):
            # write the calculation for each stat (min, max, avg) in each fan column
            worksheet.write_formula(new_row, all_col, '={formula}({col}{f_row}:{col}{l_row})'.format(
                formula=stat.upper(), col=column_letter(all_col+1), f_row=row+2, l_row=last_data_row),
                                    min_max_avg_format[stat])

        new_row += 1

    # worksheet.write(new_row, col, 'Max',     {'bold': True, 'left': 2, 'right': 1})
    # new_row += 1
    # worksheet.write(new_row, col, 'Avg', {'bold': True, 'left': 2, 'right': 1, 'bottom': 2})
    # new_row += 1

    # Add an Avg column to the right of highest fan speed; set left border, thick right border
    worksheet.write(row, new_col, 'Avg', header_format['right'])

    # Set the formula for by drive average
    for all_row in range(row+1, last_data_row):
        worksheet.write_formula(all_row, new_col, '=AVERAGE({f_col}{row}:{l_col}{row})'.format(
            row=all_row+1, f_col=column_letter(col+2), l_col=column_letter(last_data_col)),
                                workbook.add_format({'left': 1, 'right': 2}))

    # TODO: if xlsx is open, it returns IOError; catch and tell user to close
    workbook.close()


# 2 table test db
# test_db = r'C:\Users\503265\Documents\Customer_Info\Twitter\MobulaBP_ISP_030819\LatencyResults.db'
# 1 table test db
test_db = r'C:\Users\503265\Documents\Customer_Info\Twitter\MobBP_ISP_031319_rebase\LatencyResults.db'
test_xlsx = r'C:\Users\503265\Documents\Customer_Info\Twitter\MobBP_ISP_031319_rebase\test_ISP.xlsx'

chosen_table = choose_table(test_db)
print chosen_table

devs, fan_pwms = get_data(test_db, chosen_table)

layout_sheet(devs, fan_pwms, test_xlsx)
