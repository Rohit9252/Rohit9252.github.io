import React, { forwardRef, HTMLAttributes, UIEvent, useEffect, useRef, useState } from 'react'
import PropTypes from 'prop-types'
import classNames from 'classnames'

import { useForkedRef } from '../../hooks'

export interface CVirtualScrollerProps extends Omit<HTMLAttributes<HTMLDivElement>, 'onScroll'> {
  /**
   * A string of all className you want applied to the base component.
   */
  className?: string
  /**
   * Event fires when the component has been scrolled.
   */
  onScroll?: (currentItemIndex: number) => void
  /**
   * Amount of visible items
   */
  visibleItems: number
}

export const CVirtualScroller = forwardRef<HTMLDivElement, CVirtualScrollerProps>(
  ({ children, className, visibleItems, onScroll }, ref) => {
    const virtualScrollRef = useRef<HTMLDivElement>(null)
    const virtualScrollContentRef = useRef<HTMLDivElement>(null)
    const forkedRef = useForkedRef(ref, virtualScrollRef)

    const [buffer, setBuffer] = useState(Math.floor(visibleItems / 2))
    const [currentItemIndex, setCurrentItemIndex] = useState(1)
    const [itemHeight, setItemHeight] = useState(0)
    const [itemsNumber, setItemsNumber] = useState(React.Children.count(children))
    const [viewportPadding, setViewportPadding] = useState(0)
    const [viewportHeight, setViewportHeight] = useState(
      visibleItems * itemHeight + 2 * viewportPadding,
    )
    const [maxHeight, setMaxHeight] = useState(itemsNumber * itemHeight + 2 * viewportPadding)

    useEffect(() => {
      virtualScrollRef.current && virtualScrollRef.current.scrollTop

      virtualScrollRef.current &&
        setViewportPadding(Number.parseFloat(getComputedStyle(virtualScrollRef.current).paddingTop))
    })

    useEffect(() => {
      setItemsNumber(React.Children.count(children))
    }, [children])

    useEffect(() => {
      setViewportHeight(Math.min(visibleItems, itemsNumber) * itemHeight + 2 * viewportPadding)
    }, [itemHeight, itemsNumber, viewportPadding, visibleItems])

    useEffect(() => {
      setMaxHeight(itemsNumber * itemHeight)
      virtualScrollRef.current && virtualScrollRef.current.scrollTop
    }, [itemHeight, itemsNumber])

    useEffect(() => {
      setBuffer(Math.floor(visibleItems / 2))
    }, [visibleItems])

    const handleScroll = (scrollTop: number) => {
      const _currentItemIndex = itemHeight && Math.max(Math.ceil(scrollTop / itemHeight), 1)
      setCurrentItemIndex(_currentItemIndex)
      onScroll && onScroll(_currentItemIndex)
    }

    return (
      <div
        className={classNames('virtual-scroller', className)}
        onScroll={(event: UIEvent<HTMLDivElement>) =>
          handleScroll((event.target as HTMLDivElement).scrollTop)
        }
        ref={forkedRef}
        style={{
          height: viewportHeight,
          overflowY: 'auto',
        }}
      >
        <div
          className="virtual-scroller-content"
          style={{
            height: maxHeight,
          }}
          ref={virtualScrollContentRef}
        >
          {React.Children.map(children, (child, index) => {
            if (
              React.isValidElement(child) &&
              index + 1 > Math.max(currentItemIndex - buffer, 0) &&
              index + 1 <= currentItemIndex + visibleItems + buffer
            ) {
              return React.cloneElement(child as React.ReactElement<any>, {
                className: classNames(child.props.className, {
                  'virtual-scroller-item-preload':
                    index + 1 > currentItemIndex + visibleItems || index + 1 < currentItemIndex,
                }),
                key: index,
                style: {
                  ...(currentItemIndex > buffer && {
                    transform: `translateY(${(currentItemIndex - buffer) * itemHeight}px)`,
                  }),
                },
                ref: (node: HTMLElement) =>
                  node &&
                  node.offsetHeight &&
                  setItemHeight(
                    node.offsetHeight +
                      Number.parseFloat(getComputedStyle(node).marginTop) +
                      Number.parseFloat(getComputedStyle(node).marginBottom),
                  ),
              })
            }
            return
          })}
        </div>
      </div>
    )
  },
)

CVirtualScroller.propTypes = {
  onScroll: PropTypes.func,
  visibleItems: PropTypes.number.isRequired,
}

CVirtualScroller.displayName = 'CVirtualScroller'
