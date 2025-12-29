import React from 'react';
import { CButtonProps } from './../button/CButton';
export interface CLoadingButtonProps extends CButtonProps {
    /**
     * A string of all className you want applied to the base component.
     */
    className?: string;
    /**
     * Makes button disabled when loading.
     */
    disabledOnLoading?: boolean;
    /**
     * Loading state (set to true to start animation).
     */
    loading?: boolean;
    /**
     * @ignore
     */
    onClick?: () => void;
    /**
     * Sets type of spinner.
     */
    spinnerType?: 'border' | 'grow';
    /**
     * Automatically starts loading animation and stops after a determined amount of milliseconds.
     */
    timeout?: number;
}
export declare const CLoadingButton: React.ForwardRefExoticComponent<CLoadingButtonProps & React.RefAttributes<HTMLButtonElement>>;
