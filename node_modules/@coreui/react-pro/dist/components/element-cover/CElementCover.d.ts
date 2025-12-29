import React, { HTMLAttributes } from 'react';
interface CElementCoverProps extends HTMLAttributes<HTMLDivElement> {
    /**
     * A string of all className you want applied to the base component.
     */
    className?: string;
    /**
     * Array of custom boundaries. Use to create custom cover area (instead of parent element area). Area is defined by four sides: 'top', 'bottom', 'right', 'left'. If side is not defined by any custom boundary it is equal to parent element boundary. Each custom boundary is object with keys:
     * - sides (array) - select boundaries of element to define boundaries. Sides names: 'top', 'bottom', 'right', 'left'.
     * - query (string) - query used to get element which define boundaries. Search will be done only inside parent element, by parent.querySelector(query) function.
     */
    boundaries?: {
        sides: string[];
        query: string;
    }[];
    /**
     * Opacity of the cover.
     */
    opacity?: number;
}
export declare const CElementCover: React.ForwardRefExoticComponent<CElementCoverProps & React.RefAttributes<HTMLDivElement>>;
export {};
