import React, { ReactNode, HTMLAttributes } from 'react';
export interface CSmartPaginationProps extends HTMLAttributes<HTMLUListElement> {
    /**
     * A string of all className you want applied to the base component.
     */
    className?: string;
    /**
     * Current page number.
     */
    activePage?: number;
    /**
     * Show/hide dots.
     */
    dots?: boolean;
    /**
     * Show/hide arrows.
     */
    arrows?: boolean;
    /**
     * Show double arrows buttons.
     */
    doubleArrows?: boolean;
    /**
     * The content of 'firstButton' button.
     *
     * @default '<React.Fragment>&laquo;</React.Fragment>''
     */
    firstButton?: ReactNode | string;
    /**
     * The content of 'previousButton' button.
     *
     * @default '<React.Fragment>&lsaquo;</React.Fragment>'
     */
    previousButton?: ReactNode | string;
    /**
     * The content of 'nextButton' button.
     *
     * @default '<React.Fragment>&rsaquo;</React.Fragment>''
     */
    nextButton?: ReactNode | string;
    /**
     * The content of 'lastButton' button.
     *
     * @default '<React.Fragment>&raquo;</React.Fragment>'
     */
    lastButton?: ReactNode | string;
    /**
     * Size of pagination, valid values: 'sm', 'lg'.
     */
    size?: 'sm' | 'lg';
    /**
     * Horizontall align.
     */
    align?: 'start' | 'center' | 'end';
    /**
     * Maximum items number.
     */
    limit?: number;
    /**
     * Number of pages.
     */
    pages: number;
    /**
     * On active page change callback.
     */
    onActivePageChange?: (activePage: number) => void;
}
export declare const CSmartPagination: React.ForwardRefExoticComponent<CSmartPaginationProps & React.RefAttributes<HTMLUListElement>>;
