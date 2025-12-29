import React, { forwardRef } from 'react'
import PropTypes from 'prop-types'

import { CDateRangePicker, CDateRangePickerProps } from '../date-range-picker/CDateRangePicker'

export interface CDatePickerProps
  extends Omit<
    CDateRangePickerProps,
    | 'calendars'
    | 'endDate'
    | 'range'
    | 'onEndDateChange'
    | 'onStartDateChange'
    | 'ranges'
    | 'selectEndDate'
    | 'startDate'
  > {
  /**
   * Initial selected date.
   */
  date?: Date | string | null
  /**
   * The id global attribute defines an identifier (ID) that must be unique in the whole document.
   *
   * The name attribute for the input element is generated based on the `id` property:
   * - \{id\}-date
   */
  id?: string
  /**
   * Callback fired when the date changed.
   */
  onDateChange?: (date: Date | null, formatedDate?: string | undefined) => void
}

export const CDatePicker = forwardRef<HTMLDivElement | HTMLLIElement, CDatePickerProps>(
  ({ date, id, onDateChange, placeholder = 'Select date', ...rest }, ref) => {
    return (
      <CDateRangePicker
        calendars={1}
        id={id}
        startDate={date}
        onStartDateChange={onDateChange}
        placeholder={placeholder}
        range={false}
        ref={ref}
        {...rest}
      />
    )
  },
)

CDatePicker.displayName = 'CDatePicker'

CDatePicker.propTypes = {
  ...CDateRangePicker.propTypes,
  date: PropTypes.oneOfType([PropTypes.instanceOf(Date), PropTypes.string]),
  onDateChange: PropTypes.func,
}
