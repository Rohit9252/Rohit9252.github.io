import React, { forwardRef, useEffect, useRef } from 'react'
import PropTypes from 'prop-types'
import classNames from 'classnames'

import { useForkedRef, useIsVisible } from '../../hooks'

export interface Element {
  value: number | string
  label: number | string
}

export interface CTimePickerRollColProps {
  elements: Element[]
  onClick?: (value: number | string) => void
  selected?: number | string | null
}

export const CTimePickerRollCol = forwardRef<HTMLDivElement, CTimePickerRollColProps>(
  ({ elements, onClick, selected }, ref) => {
    const init = useRef(true)
    const colRef = useRef<HTMLDivElement>(null)
    const forkedRef = useForkedRef(ref, colRef)
    const isVisible = useIsVisible(colRef)

    useEffect(() => {
      const nodeEl = colRef.current?.querySelector('.selected')
      if (isVisible && nodeEl && nodeEl instanceof HTMLElement) {
        colRef.current?.scrollTo({
          top: nodeEl.offsetTop,
          behavior: init.current ? 'auto' : 'smooth',
        })
      }

      if (isVisible) {
        init.current = false
      }
    }, [isVisible, selected])

    const handleKeyDown = (event: React.KeyboardEvent<HTMLDivElement>, value: number | string) => {
      if (event.code === 'Space' || event.key === 'Enter') {
        event.preventDefault()
        onClick && onClick(value)
      }
    }

    return (
      <div className="time-picker-roll-col" ref={forkedRef}>
        {elements.map((element, index) => {
          return (
            <div
              className={classNames('time-picker-roll-cell', {
                selected: element.value === selected,
              })}
              key={index}
              onClick={() => onClick && onClick(element.value)}
              onKeyDown={(event) => handleKeyDown(event, element.value)}
              role="button"
              tabIndex={0}
            >
              {element.label}
            </div>
          )
        })}
      </div>
    )
  },
)

CTimePickerRollCol.propTypes = {
  elements: PropTypes.array.isRequired,
  onClick: PropTypes.func,
  selected: PropTypes.oneOfType([PropTypes.number, PropTypes.string]),
}

CTimePickerRollCol.displayName = 'CTimePickerRollCol'
