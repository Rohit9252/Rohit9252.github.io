import React from 'react';
import { CDateRangePickerProps } from '../date-range-picker/CDateRangePicker';
export interface CDatePickerProps extends Omit<CDateRangePickerProps, 'calendars' | 'endDate' | 'range' | 'onEndDateChange' | 'onStartDateChange' | 'ranges' | 'selectEndDate' | 'startDate'> {
    /**
     * Initial selected date.
     */
    date?: Date | string | null;
    /**
     * The id global attribute defines an identifier (ID) that must be unique in the whole document.
     *
     * The name attribute for the input element is generated based on the `id` property:
     * - \{id\}-date
     */
    id?: string;
    /**
     * Callback fired when the date changed.
     */
    onDateChange?: (date: Date | null, formatedDate?: string | undefined) => void;
}
export declare const CDatePicker: React.ForwardRefExoticComponent<CDatePickerProps & React.RefAttributes<HTMLDivElement | HTMLLIElement>>;
