import React, { MouseEvent, ReactNode } from 'react';
import { CTableBodyProps } from '../table/CTableBody';
import type { Item, ScopedColumns } from './types';
export interface CSmartTableBodyProps extends CTableBodyProps {
    clickableRows?: boolean;
    columnNames: string[];
    currentItems: Item[];
    firstItemOnActivePageIndex: number;
    noItemsLabel?: string | ReactNode;
    onRowChecked?: (item: Item, value: boolean) => void;
    onRowClick?: (item: Item, index: number, columnName: string, event: MouseEvent | boolean) => void;
    scopedColumns?: ScopedColumns;
    selectable?: boolean;
    selected?: Item[];
}
export declare const CSmartTableBody: React.ForwardRefExoticComponent<CSmartTableBodyProps & React.RefAttributes<HTMLTableSectionElement>>;
