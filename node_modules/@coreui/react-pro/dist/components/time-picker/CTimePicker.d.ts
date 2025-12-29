import React, { ReactNode } from 'react';
import { CFormControlWrapperProps } from '../form/CFormControlWrapper';
import { CPickerProps } from './../picker/CPicker';
import { Colors } from '../../types';
export interface CTimePickerProps extends Omit<CFormControlWrapperProps, 'floatingLabel'>, Omit<CPickerProps, 'placeholder'> {
    /**
     * Set if the component should use the 12/24 hour format. If `true` forces the interface to a 12-hour format. If `false` forces the interface into a 24-hour format. If `auto` the current locale will determine the 12 or 24-hour interface by default locales.
     *
     * @since 4.8.0
     */
    ampm?: 'auto' | boolean;
    /**
     * A string of all className you want applied to the component.
     */
    className?: string;
    /**
     * Toggle visibility or set the content of cancel button.
     */
    cancelButton?: boolean | ReactNode;
    /**
     * Sets the color context of the cancel button to one of CoreUI’s themed colors.
     *
     * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | string
     */
    cancelButtonColor?: Colors;
    /**
     * Size the cancel button small or large.
     */
    cancelButtonSize?: 'sm' | 'lg';
    /**
     * Set the cancel button variant to an outlined button or a ghost button.
     */
    cancelButtonVariant?: 'outline' | 'ghost';
    /**
     * A string of all className you want applied to the component.
     */
    /**
     * Toggle visibility or set the content of the cleaner button.
     */
    cleaner?: ReactNode | boolean;
    /**
     * Toggle visibility or set the content of confirm button.
     */
    confirmButton?: boolean | ReactNode;
    /**
     * Sets the color context of the confirm button to one of CoreUI’s themed colors.
     *
     * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | string
     */
    confirmButtonColor?: Colors;
    /**
     * Size the confirm button small or large.
     */
    confirmButtonSize?: 'sm' | 'lg';
    /**
     * Set the confirm button variant to an outlined button or a ghost button.
     */
    confirmButtonVariant?: 'outline' | 'ghost';
    /**
     * Toggle visibility or set the content of the input indicator.
     */
    indicator?: ReactNode | boolean;
    /**
     * Toggle the readonly state for the component.
     */
    inputReadOnly?: boolean;
    /**
     * Sets the default locale for components. If not set, it is inherited from the browser.
     */
    locale?: string;
    /**
     * Callback fired when the time changed.
     */
    onTimeChange?: (timeString: string | null, localeTimeString?: string, date?: Date) => void;
    /**
     * Specifies a short hint that is visible in the input.
     */
    placeholder?: string;
    /**
     * When present, it specifies that time must be filled out before submitting the form.
     *
     * @since 4.10.0
     */
    required?: boolean;
    /**
     * Show seconds.
     *
     * @since 4.8.0
     */
    seconds?: boolean;
    /**
     * Size the component small or large.
     */
    size?: 'sm' | 'lg';
    /**
     * Initial selected time.
     */
    time?: Date | string | null;
    /**
     * Set the time picker variant to a roll or select.
     */
    variant?: 'roll' | 'select';
}
export declare const CTimePicker: React.ForwardRefExoticComponent<CTimePickerProps & React.RefAttributes<HTMLDivElement | HTMLLIElement>>;
