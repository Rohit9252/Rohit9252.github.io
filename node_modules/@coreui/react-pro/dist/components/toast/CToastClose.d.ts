import React, { ElementType } from 'react';
import { CButtonProps } from '../button/CButton';
import { CCloseButtonProps } from '../close-button/CCloseButton';
type CombineButtonProps = CCloseButtonProps & CButtonProps;
export interface CToastCloseProps extends CombineButtonProps {
    /**
     * Component used for the root node. Either a string to use a HTML element or a component.
     */
    component?: string | ElementType;
}
export declare const CToastClose: React.ForwardRefExoticComponent<CToastCloseProps & React.RefAttributes<HTMLButtonElement>>;
export {};
