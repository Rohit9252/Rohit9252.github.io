import React, { HTMLAttributes } from 'react';
import type { Colors, Gradients } from '../../types';
export interface CCardProps extends HTMLAttributes<HTMLDivElement> {
    /**
     * A string of all className you want applied to the base component.
     */
    className?: string;
    /**
     * Sets the color context of the component to one of CoreUI’s themed colors.
     *
     * @type {'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | 'primary-gradient' | 'secondary-gradient' | 'success-gradient' | 'danger-gradient' | 'warning-gradient' | 'info-gradient' | 'dark-gradient' | 'light-gradient' | string }
     */
    color?: Colors | Gradients;
    /**
     * Sets the text color context of the component to one of CoreUI’s themed colors.
     *
     * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | 'white' | 'muted' | 'high-emphasis' | 'medium-emphasis' | 'disabled' | 'high-emphasis-inverse' | 'medium-emphasis-inverse' | 'disabled-inverse' | string
     */
    textColor?: string;
}
export declare const CCard: React.ForwardRefExoticComponent<CCardProps & React.RefAttributes<HTMLDivElement>>;
