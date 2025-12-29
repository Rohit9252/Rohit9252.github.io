import React, { ElementType, ReactNode } from 'react';
import { CTableHeadProps } from '../table/CTableHead';
import type { ColumnFilter, ColumnFilterValue, Column, Item, Sorter, SorterValue } from './types';
export interface CSmartTableHeadProps extends CTableHeadProps {
    columnFilter?: boolean | ColumnFilter;
    columnFilterState?: ColumnFilterValue;
    columnSorter?: boolean | Sorter;
    component?: string | ElementType;
    columns: (Column | string)[];
    handleOnCustomFilterChange?: (key: string, value: any) => void;
    handleFilterOnChange?: (key: string, value: string) => void;
    handleFilterOnInput?: (key: string, value: string) => void;
    handleSelectAllChecked?: () => void;
    handleSort?: (key: string, index: number) => void;
    items: Item[];
    selectable?: boolean;
    selectAll?: boolean | {
        external?: boolean;
    };
    selectedAll?: boolean | string;
    showGroups?: boolean;
    sorterState?: SorterValue;
    sortingIcon?: ReactNode;
    sortingIconAscending?: ReactNode;
    sortingIconDescending?: ReactNode;
}
export declare const CSmartTableHead: React.ForwardRefExoticComponent<CSmartTableHeadProps & React.RefAttributes<HTMLTableSectionElement>>;
