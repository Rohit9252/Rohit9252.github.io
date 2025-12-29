import React, { ReactNode } from 'react';
export interface CCalendarProps {
    /**
     * Default date of the component
     */
    calendarDate?: Date | string;
    /**
     * The number of calendars that render on desktop devices.
     */
    calendars?: number;
    /**
     * A string of all className you want applied to the component.
     */
    className?: string;
    /**
     * Set the format of day name.
     *
     * @default 'numeric'
     * @since 4.3.0
     */
    dayFormat?: 'numeric' | '2-digit' | ((date: Date) => string | number);
    /**
     * Specify the list of dates that cannot be selected.
     */
    disabledDates?: Date[] | Date[][] | (Date | Date[])[];
    /**
     * Initial selected to date (range).
     */
    endDate?: Date | string | null;
    /**
     * Sets the day of start week.
     * - 0 - Sunday,
     * - 1 - Monday,
     * - 2 - Tuesday,
     * - 3 - Wednesday,
     * - 4 - Thursday,
     * - 5 - Friday,
     * - 6 - Saturday,
     *
     * @default 1
     */
    firstDayOfWeek?: number;
    /**
     * Sets the default locale for components. If not set, it is inherited from the browser.
     *
     * @default 'default'
     */
    locale?: string;
    /**
     * Max selectable date.
     */
    maxDate?: Date | string | null;
    /**
     * Min selectable date.
     */
    minDate?: Date | string | null;
    /**
     * Show arrows navigation.
     */
    navigation?: boolean;
    /**
     * The custom next icon.
     */
    navNextIcon?: ReactNode;
    /**
     * The custom next double icon.
     */
    navNextDoubleIcon?: ReactNode;
    /**
     * The custom prev icon.
     */
    navPrevIcon?: ReactNode;
    /**
     * The custom prev double icon.
     */
    navPrevDoubleIcon?: ReactNode;
    /**
     * Reorder year-month navigation, and render year first.
     *
     * @since 4.3.0
     */
    navYearFirst?: boolean;
    /**
     * Set whether days in adjacent months shown before or after the current month are selectable. This only applies if the `showAdjacementDays` option is set to true.
     *
     * @since 4.11.0
     */
    selectAdjacementDays?: boolean;
    /**
     * Set whether to display dates in adjacent months (non-selectable) at the start and end of the current month.
     *
     * @since 4.11.0
     */
    showAdjacementDays?: boolean;
    /**
     * Allow range selection.
     */
    range?: boolean;
    /**
     * Toggle select mode between start and end date.
     */
    selectEndDate?: boolean;
    /**
     * Initial selected date.
     */
    startDate?: Date | string | null;
    /**
     * Set length or format of day name.
     *
     * @default 2
     */
    weekdayFormat?: number | 'long' | 'narrow' | 'short' | ((date: Date) => string | number);
    /**
     * Callback fired when the calendar date changed.
     */
    onCalendarDateChange?: (date: Date) => void;
    /**
     * Callback fired when the user hovers over the calendar cell.
     */
    onDayHover?: (date: Date | null) => void;
    /**
     * Callback fired when the start date changed.
     */
    onStartDateChange?: (date: Date | null, formatedDate?: string | undefined) => void;
    /**
     * Callback fired when the end date changed.
     */
    onEndDateChange?: (date: Date | null, formatedDate?: string | undefined) => void;
    /**
     * Callback fired when the selection type changed.
     */
    onSelectEndChange?: (value: boolean) => void;
    /**
     * Callback fired when the view type of calendar changed.
     */
    onViewChanged?: (view: string) => void;
}
export declare const CCalendar: React.ForwardRefExoticComponent<CCalendarProps & React.RefAttributes<HTMLDivElement>>;
