import React, { InputHTMLAttributes } from 'react';
import type { Option } from './types';
export interface CMultiSelectNativeSelectProps extends Omit<InputHTMLAttributes<HTMLSelectElement>, 'options'> {
    options?: Option[];
    value?: string | number | string[];
}
export declare const CMultiSelectNativeSelect: React.ForwardRefExoticComponent<CMultiSelectNativeSelectProps & React.RefAttributes<HTMLSelectElement>>;
