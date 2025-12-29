import React, { HTMLAttributes, ReactNode } from 'react';
import { CFormControlWrapperProps } from '../form/CFormControlWrapper';
import type { Option, OptionsGroup } from './types';
export interface CMultiSelectProps extends Omit<CFormControlWrapperProps, 'floatingClassName' | 'floatingLabel'>, Omit<HTMLAttributes<HTMLDivElement>, 'onChange'> {
    /**
     * Allow users to create options if they are not in the list of options.
     *
     * @since 4.11.0
     */
    allowCreateOptions?: boolean;
    /**
     * A string of all className you want applied to the base component.
     */
    className?: string;
    /**
     * Enables selection cleaner element.
     */
    cleaner?: boolean;
    /**
     * Clear current search on selecting an item.
     *
     * @since 4.11.0
     */
    clearSearchOnSelect?: boolean;
    /**
     * Toggle the disabled state for the component.
     */
    disabled?: boolean;
    /**
     * The id global attribute defines an identifier (ID) that must be unique in the whole document.
     *
     * The name and id attributes for the native select element are generated based on the `id` property:
     * - <select id="\{id\}-multi-select" name="\{id\}-multi-select" />
     */
    id?: string;
    /**
     * When set, the options list will have a loading style: loading spinner and reduced opacity.
     *
     * @since 4.11.0
     */
    loading?: boolean;
    /**
     * It specifies that multiple options can be selected at once.
     */
    multiple?: boolean;
    /**
     * Execute a function when a user changes the selected option.
     */
    onChange?: (selected: Option[]) => void;
    /**
     * Execute a function when the filter value changed.
     *
     * @since 4.8.0
     */
    onFilterChange?: (value: string) => void;
    /**
     * The callback is fired when the Multi Select component requests to be hidden.
     */
    onHide?: () => void;
    /**
     * The callback is fired when the Multi Select component requests to be shown.
     */
    onShow?: () => void;
    /**
     * List of option elements.
     */
    options: (Option | OptionsGroup)[];
    /**
     * Sets maxHeight of options list.
     */
    optionsMaxHeight?: number | string;
    /**
     * Sets option style.
     */
    optionsStyle?: 'checkbox' | 'text';
    /**
     * Custom template for options.
     *
     * @since 4.12.0
     */
    optionsTemplate?: (option: Option) => ReactNode;
    /**
     * Custom template for options groups.
     *
     * @since 4.12.0
     */
    optionsGroupsTemplate?: (option: OptionsGroup) => ReactNode;
    /**
     * Specifies a short hint that is visible in the search input.
     */
    placeholder?: string;
    /**
     * When it is present, it indicates that the user must choose a value before submitting the form.
     */
    required?: boolean;
    /**
     * Enables search input element.
     */
    search?: boolean | 'external';
    /**
     * Sets the label for no results when filtering.
     */
    searchNoResultsLabel?: string | ReactNode;
    /**
     * Enables select all button.
     */
    selectAll?: boolean;
    /**
     * Sets the select all button label.
     */
    selectAllLabel?: string | ReactNode;
    /**
     * Sets the selection style.
     */
    selectionType?: 'counter' | 'tags' | 'text';
    /**
     * Sets the counter selection label.
     */
    selectionTypeCounterText?: string;
    /**
     * Size the component small or large.
     */
    size?: 'sm' | 'lg';
    /**
     * Enable virtual scroller for the options list.
     *
     * @since 4.8.0
     */
    virtualScroller?: boolean;
    /**
     * Toggle the visibility of multi select dropdown.
     */
    visible?: boolean;
    /**
     * Amount of visible items when virtualScroller is set to `true`.
     *
     * @since 4.8.0
     */
    visibleItems?: number;
}
export declare const CMultiSelect: React.ForwardRefExoticComponent<CMultiSelectProps & React.RefAttributes<HTMLDivElement>>;
