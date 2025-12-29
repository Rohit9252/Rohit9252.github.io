import React, { HTMLAttributes } from 'react';
interface CSmartTableFilterProps extends HTMLAttributes<HTMLInputElement> {
    filterLabel?: string;
    filterPlaceholder?: string;
    value?: string | number;
}
export declare const CSmartTableFilter: React.ForwardRefExoticComponent<CSmartTableFilterProps & React.RefAttributes<HTMLInputElement>>;
export {};
