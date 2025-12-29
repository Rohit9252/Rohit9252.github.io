import React, { HTMLAttributes } from 'react';
interface CSmartTableItemsPerPageSelectorProps extends HTMLAttributes<HTMLSelectElement> {
    itemsPerPage?: number;
    itemsPerPageLabel?: string;
    itemsPerPageOptions?: number[];
}
export declare const CSmartTableItemsPerPageSelector: React.ForwardRefExoticComponent<CSmartTableItemsPerPageSelectorProps & React.RefAttributes<HTMLSelectElement>>;
export {};
