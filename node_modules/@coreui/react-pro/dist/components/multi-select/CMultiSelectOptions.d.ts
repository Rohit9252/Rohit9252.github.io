import React, { HTMLAttributes, ReactNode } from 'react';
import type { Option, OptionsGroup } from './types';
export interface CMultiSelectOptionsProps extends HTMLAttributes<HTMLDivElement> {
    handleOptionOnClick?: (option: Option) => void;
    loading?: boolean;
    options: (Option | OptionsGroup)[];
    optionsMaxHeight?: number | string;
    optionsStyle?: 'checkbox' | 'text';
    optionsTemplate?: (option: Option) => ReactNode;
    optionsGroupsTemplate?: (option: OptionsGroup) => ReactNode;
    searchNoResultsLabel?: string | ReactNode;
    selected: Option[];
    virtualScroller?: boolean;
    visibleItems?: number;
}
export declare const CMultiSelectOptions: React.ForwardRefExoticComponent<CMultiSelectOptionsProps & React.RefAttributes<HTMLDivElement>>;
