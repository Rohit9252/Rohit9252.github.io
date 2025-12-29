import React, { HTMLAttributes } from 'react';
export interface CVirtualScrollerProps extends Omit<HTMLAttributes<HTMLDivElement>, 'onScroll'> {
    /**
     * A string of all className you want applied to the base component.
     */
    className?: string;
    /**
     * Event fires when the component has been scrolled.
     */
    onScroll?: (currentItemIndex: number) => void;
    /**
     * Amount of visible items
     */
    visibleItems: number;
}
export declare const CVirtualScroller: React.ForwardRefExoticComponent<CVirtualScrollerProps & React.RefAttributes<HTMLDivElement>>;
