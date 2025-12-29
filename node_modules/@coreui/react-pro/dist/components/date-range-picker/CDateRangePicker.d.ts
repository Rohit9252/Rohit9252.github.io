import React, { ReactNode } from 'react';
import { CCalendarProps } from '../calendar/CCalendar';
import { CFormControlWrapperProps } from '../form/CFormControlWrapper';
import { CPickerProps } from '../picker/CPicker';
import { Colors } from '../../types';
export interface CDateRangePickerProps extends Omit<CFormControlWrapperProps, 'floatingLabel'>, Omit<CPickerProps, 'placeholder'>, Omit<CCalendarProps, 'onDayHover' | 'onCalendarDateChange'> {
    /**
     * The number of calendars that render on desktop devices.
     */
    calendars?: number;
    /**
     * Toggle visibility or set the content of cancel button.
     *
     * @default 'Cancel'
     */
    cancelButton?: boolean | ReactNode;
    /**
     * Sets the color context of the cancel button to one of CoreUI’s themed colors.
     *
     * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | string
     * @default 'primary'
     */
    cancelButtonColor?: Colors;
    /**
     * Size the cancel button small or large.
     *
     * @default 'sm'
     */
    cancelButtonSize?: 'sm' | 'lg';
    /**
     * Set the cancel button variant to an outlined button or a ghost button.
     *
     * @default 'ghost'
     */
    cancelButtonVariant?: 'outline' | 'ghost';
    /**
     * A string of all className you want applied to the component.
     */
    className?: string;
    /**
     * If true the dropdown will be immediately closed after submitting the full date.
     *
     * @since 4.8.0
     */
    closeOnSelect?: boolean;
    /**
     * Toggle visibility or set the content of the cleaner button.
     */
    cleaner?: boolean;
    /**
     * Toggle visibility or set the content of confirm button.
     *
     * @default 'OK'
     */
    confirmButton?: boolean | ReactNode;
    /**
     * Sets the color context of the confirm button to one of CoreUI’s themed colors.
     *
     * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | string
     * @default 'primary'
     */
    confirmButtonColor?: Colors;
    /**
     * Size the confirm button small or large.
     *
     * @default 'sm'
     */
    confirmButtonSize?: 'sm' | 'lg';
    /**
     * Set the confirm button variant to an outlined button or a ghost button.
     */
    confirmButtonVariant?: 'outline' | 'ghost';
    /**
     * Set date format.
     * We use date-fns to format dates. Visit https://date-fns.org/v2.28.0/docs/format to check accepted patterns.
     */
    format?: string;
    /**
     * The id global attribute defines an identifier (ID) that must be unique in the whole document.
     *
     * The name attributes for input elements are generated based on the `id` property:
     * - \{id\}-start-date
     * - \{id\}-end-date
     */
    id?: string;
    /**
     * Toggle visibility or set the content of the input indicator.
     */
    indicator?: ReactNode | boolean;
    /**
     * Custom function to format the selected date into a string according to a custom format.
     *
     * @since v4.14.0
     */
    inputDateFormat?: (date: Date) => string;
    /**
     * Custom function to parse the input value into a valid Date object.
     *
     * @since v4.14.0
     */
    inputDateParse?: (date: string | Date) => Date;
    /**
     * Defines the delay (in milliseconds) for the input field's onChange event.
     *
     * @since v4.14.0
     */
    inputOnChangeDelay?: number;
    /**
     * Toggle the readonly state for the component.
     */
    inputReadOnly?: boolean;
    /**
     * Specifies short hints that are visible in start date and end date inputs.
     */
    placeholder?: string | string[];
    /**
     * @ignore
     */
    range?: boolean;
    /**
     * Predefined date ranges the user can select from.
     */
    ranges?: object;
    /**
     * Sets the color context of the cancel button to one of CoreUI’s themed colors.
     *
     * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | string
     */
    rangesButtonsColor?: Colors;
    /**
     * Size the ranges button small or large.
     */
    rangesButtonsSize?: 'sm' | 'lg';
    /**
     * Set the ranges button variant to an outlined button or a ghost button.
     */
    rangesButtonsVariant?: 'outline' | 'ghost';
    /**
     * When present, it specifies that date must be filled out before submitting the form.
     *
     * @since 4.10.0
     */
    required?: boolean;
    /**
     * Default icon or character character that separates two dates.
     */
    separator?: ReactNode | boolean;
    /**
     * Size the component small or large.
     */
    size?: 'sm' | 'lg';
    /**
     * Provide an additional time selection by adding select boxes to choose times.
     */
    timepicker?: boolean;
    /**
     * Toggle visibility or set the content of today button.
     *
     * @default 'Today'
     */
    todayButton?: boolean | ReactNode;
    /**
     * Sets the color context of the today button to one of CoreUI’s themed colors.
     *
     * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | string
     * @default 'primary'
     */
    todayButtonColor?: Colors;
    /**
     * Size the today button small or large.
     *
     * @default 'sm'
     */
    todayButtonSize?: 'sm' | 'lg';
    /**
     * Set the today button variant to an outlined button or a ghost button.
     */
    todayButtonVariant?: 'outline' | 'ghost';
}
export declare const CDateRangePicker: React.ForwardRefExoticComponent<CDateRangePickerProps & React.RefAttributes<HTMLDivElement | HTMLLIElement>>;
