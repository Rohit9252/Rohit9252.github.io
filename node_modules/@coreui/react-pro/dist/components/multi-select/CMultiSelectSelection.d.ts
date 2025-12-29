import React, { HTMLAttributes } from 'react';
import type { SelectedOption } from './types';
export interface CMultiSelectSelectionProps extends HTMLAttributes<HTMLSpanElement> {
    multiple?: boolean;
    onRemove?: (option: SelectedOption) => void;
    placeholder?: string;
    search?: boolean | 'external';
    selected?: SelectedOption[];
    selectionType?: 'counter' | 'tags' | 'text';
    selectionTypeCounterText?: string;
}
export declare const CMultiSelectSelection: React.ForwardRefExoticComponent<CMultiSelectSelectionProps & React.RefAttributes<HTMLSpanElement>>;
