import React, { ElementType, HTMLAttributes } from 'react';
export interface CHeaderBrandProps extends HTMLAttributes<HTMLAnchorElement | HTMLLinkElement | HTMLSpanElement> {
    /**
     * A string of all className you want applied to the component.
     */
    className?: string;
    /**
     * Component used for the root node. Either a string to use a HTML element or a component.
     */
    component?: string | ElementType;
    /**
     * The href attribute specifies the URL of the page the link goes to.
     */
    href?: string;
}
export declare const CHeaderBrand: React.ForwardRefExoticComponent<CHeaderBrandProps & React.RefAttributes<HTMLLinkElement | HTMLAnchorElement | HTMLSpanElement>>;
