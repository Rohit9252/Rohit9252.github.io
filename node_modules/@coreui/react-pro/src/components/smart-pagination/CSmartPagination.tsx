import React, { forwardRef, ReactNode, HTMLAttributes } from 'react'
import classNames from 'classnames'
import PropTypes from 'prop-types'

import { CPagination, CPaginationItem } from './../pagination'

export interface CSmartPaginationProps extends HTMLAttributes<HTMLUListElement> {
  /**
   * A string of all className you want applied to the base component.
   */
  className?: string
  /**
   * Current page number.
   */
  activePage?: number
  /**
   * Show/hide dots.
   */
  dots?: boolean
  /**
   * Show/hide arrows.
   */
  arrows?: boolean
  /**
   * Show double arrows buttons.
   */
  doubleArrows?: boolean
  /**
   * The content of 'firstButton' button.
   *
   * @default '<React.Fragment>&laquo;</React.Fragment>''
   */
  firstButton?: ReactNode | string
  /**
   * The content of 'previousButton' button.
   *
   * @default '<React.Fragment>&lsaquo;</React.Fragment>'
   */
  previousButton?: ReactNode | string
  /**
   * The content of 'nextButton' button.
   *
   * @default '<React.Fragment>&rsaquo;</React.Fragment>''
   */
  nextButton?: ReactNode | string
  /**
   * The content of 'lastButton' button.
   *
   * @default '<React.Fragment>&raquo;</React.Fragment>'
   */
  lastButton?: ReactNode | string
  /**
   * Size of pagination, valid values: 'sm', 'lg'.
   */
  size?: 'sm' | 'lg'
  /**
   * Horizontall align.
   */
  align?: 'start' | 'center' | 'end'
  /**
   * Maximum items number.
   */
  limit?: number
  /**
   * Number of pages.
   */
  pages: number
  /**
   * On active page change callback.
   */
  onActivePageChange?: (activePage: number) => void
}

export const CSmartPagination = forwardRef<HTMLUListElement, CSmartPaginationProps>(
  (
    {
      className,
      activePage = 1,
      align = 'start',
      arrows = true,
      dots = true,
      doubleArrows = true,
      firstButton = <React.Fragment>&laquo;</React.Fragment>,
      lastButton = <React.Fragment>&raquo;</React.Fragment>,
      limit = 5,
      nextButton = <React.Fragment>&rsaquo;</React.Fragment>,
      onActivePageChange,
      pages,
      previousButton = <React.Fragment>&lsaquo;</React.Fragment>,
      size,
      ...rest
    },
    ref,
  ) => {
    const showDots: boolean = (() => {
      return dots && limit > 4 && limit < pages
    })()

    const maxPrevItems: number = (() => {
      return Math.floor((limit - 1) / 2)
    })()

    const maxNextItems: number = (() => {
      return Math.ceil((limit - 1) / 2)
    })()

    const beforeDots: boolean = (() => {
      return showDots && activePage > maxPrevItems + 1
    })()

    const afterDots: boolean = (() => {
      return showDots && activePage < pages - maxNextItems
    })()

    const computedLimit: number = (() => {
      return limit - (afterDots ? 1 : 0) - (beforeDots ? 1 : 0)
    })()

    const range: number = (() => {
      return activePage + maxNextItems
    })()

    const lastItem: number = (() => {
      return range >= pages ? pages : range - (afterDots ? 1 : 0)
    })()

    const itemsAmount: number = (() => {
      return pages < computedLimit ? pages : computedLimit
    })()

    const items: number[] = (() => {
      return activePage - maxPrevItems <= 1
        ? Array.from(
            {
              length: itemsAmount,
            },
            (_v, i) => i + 1,
          )
        : Array.from(
            {
              length: itemsAmount,
            },
            (_v, i) => {
              return lastItem - i
            },
          ).reverse()
    })()

    const setPage = (number: number): void => {
      if (number !== activePage) {
        onActivePageChange && onActivePageChange(number)
      }
    }

    return (
      <CPagination
        className={classNames(`justify-content-${align}`, className)}
        aria-label="pagination"
        size={size}
        {...rest}
        ref={ref}
      >
        {doubleArrows && (
          <CPaginationItem
            onClick={() => setPage(1)}
            aria-label="Go to first page"
            aria-disabled={activePage === 1}
            disabled={activePage === 1}
          >
            {firstButton}
          </CPaginationItem>
        )}
        {arrows && (
          <CPaginationItem
            onClick={() => setPage(activePage - 1)}
            aria-label="Go to previous page"
            aria-disabled={activePage === 1}
            disabled={activePage === 1}
          >
            {previousButton}
          </CPaginationItem>
        )}
        {beforeDots && (
          <CPaginationItem role="separator" disabled>
            …
          </CPaginationItem>
        )}
        {items.map((i) => {
          return (
            <CPaginationItem
              onClick={() => setPage(i)}
              aria-label={activePage === i ? `Current page ${i}` : `Go to page ${i}`}
              active={activePage === i}
              key={i}
            >
              {i}
            </CPaginationItem>
          )
        })}
        {afterDots && (
          <CPaginationItem role="separator" disabled>
            …
          </CPaginationItem>
        )}
        {arrows && (
          <CPaginationItem
            onClick={() => setPage(activePage + 1)}
            aria-label="Go to next page"
            aria-disabled={activePage === pages}
            disabled={activePage === pages}
          >
            {nextButton}
          </CPaginationItem>
        )}
        {doubleArrows && (
          <CPaginationItem
            onClick={() => setPage(pages)}
            aria-label="Go to last page"
            aria-disabled={activePage === pages}
            disabled={activePage === pages}
          >
            {lastButton}
          </CPaginationItem>
        )}
      </CPagination>
    )
  },
)

CSmartPagination.propTypes = {
  className: PropTypes.oneOfType([PropTypes.string]),
  activePage: PropTypes.number,
  dots: PropTypes.bool,
  arrows: PropTypes.bool,
  doubleArrows: PropTypes.bool,
  firstButton: PropTypes.oneOfType([PropTypes.node, PropTypes.string]),
  previousButton: PropTypes.oneOfType([PropTypes.node, PropTypes.string]),
  nextButton: PropTypes.oneOfType([PropTypes.node, PropTypes.string]),
  lastButton: PropTypes.oneOfType([PropTypes.node, PropTypes.string]),
  size: PropTypes.oneOf(['sm', 'lg']),
  align: PropTypes.oneOf(['start', 'center', 'end']),
  limit: PropTypes.number,
  pages: PropTypes.number.isRequired,
  onActivePageChange: PropTypes.func,
}

CSmartPagination.displayName = 'CSmartPagination'
