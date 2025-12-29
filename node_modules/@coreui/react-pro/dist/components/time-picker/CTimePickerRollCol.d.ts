import React from 'react';
export interface Element {
    value: number | string;
    label: number | string;
}
export interface CTimePickerRollColProps {
    elements: Element[];
    onClick?: (value: number | string) => void;
    selected?: number | string | null;
}
export declare const CTimePickerRollCol: React.ForwardRefExoticComponent<CTimePickerRollColProps & React.RefAttributes<HTMLDivElement>>;
