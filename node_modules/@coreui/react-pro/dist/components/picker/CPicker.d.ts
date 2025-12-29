import React, { HTMLAttributes, ReactNode } from 'react';
export interface CPickerProps extends HTMLAttributes<HTMLDivElement> {
    /**
     * Set container type for the component.
     */
    container?: 'dropdown' | 'inline';
    /**
     * Toggle the disabled state for the component.
     */
    disabled?: boolean;
    /**
     * A string of all className you want applied to the dropdown menu.
     */
    dropdownClassNames?: string;
    /**
     * Toggle visibility of footer element or set the content of footer.
     */
    footer?: boolean | ReactNode;
    /**
     * Add custom elements to the footer.
     */
    footerContent?: ReactNode;
    /**
     * Callback fired when the component requests to be hidden.
     */
    onHide?: () => void;
    /**
     * Callback fired when the component requests to be shown.
     */
    onShow?: () => void;
    /**
     * The content of toggler.
     */
    toggler?: ReactNode;
    /**
     * Toggle the visibility of dropdown menu component.
     */
    visible?: boolean;
}
export declare const CPicker: React.ForwardRefExoticComponent<CPickerProps & React.RefAttributes<HTMLDivElement | HTMLLIElement>>;
