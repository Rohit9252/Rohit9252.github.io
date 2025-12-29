import React, { forwardRef, HTMLAttributes } from 'react'

import classNames from 'classnames'
import PropTypes from 'prop-types'

import type { SelectedOption } from './types'

export interface CMultiSelectSelectionProps extends HTMLAttributes<HTMLSpanElement> {
  multiple?: boolean
  onRemove?: (option: SelectedOption) => void
  placeholder?: string
  search?: boolean | 'external'
  selected?: SelectedOption[]
  selectionType?: 'counter' | 'tags' | 'text'
  selectionTypeCounterText?: string
}

export const CMultiSelectSelection = forwardRef<HTMLSpanElement, CMultiSelectSelectionProps>(
  (
    {
      children,
      multiple,
      placeholder,
      onRemove,
      search,
      selected = [],
      selectionType,
      selectionTypeCounterText,
    },
    ref,
  ) => {
    return (
      <span
        className={classNames('form-multi-select-selection', {
          'form-multi-select-selection-tags': multiple && selectionType === 'tags',
        })}
        ref={ref}
      >
        {multiple && selectionType === 'counter' && !search && selected.length === 0 && placeholder}
        {multiple &&
          selectionType === 'counter' &&
          !search &&
          selected.length > 0 &&
          `${selected.length} ${selectionTypeCounterText}`}
        {multiple &&
          selectionType === 'tags' &&
          selected.map((option: SelectedOption, index: number) => {
            if (selectionType === 'tags') {
              return (
                <span className="form-multi-select-tag" key={index}>
                  {option.text}
                  {!option.disabled && (
                    <button
                      className="form-multi-select-tag-delete"
                      aria-label="Close"
                      onClick={() => onRemove && onRemove(option)}
                    >
                      <span aria-hidden="true">×</span>
                    </button>
                  )}
                </span>
              )
            }
            return
          })}
        {multiple &&
          selectionType === 'text' &&
          selected.map((option, index) => (
            <span key={index}>
              {option.text}
              {index === selected.length - 1 ? '' : ','}&nbsp;
            </span>
          ))}
        {!multiple && !search && selected.map((option) => option.text)[0]}
        {children}
      </span>
    )
  },
)

CMultiSelectSelection.propTypes = {
  multiple: PropTypes.bool,
  onRemove: PropTypes.func,
  placeholder: PropTypes.string,
  search: PropTypes.oneOfType([PropTypes.bool, PropTypes.oneOf<'external'>(['external'])]),
  selected: PropTypes.array,
  selectionType: PropTypes.oneOf(['counter', 'tags', 'text']),
  selectionTypeCounterText: PropTypes.string,
}

CMultiSelectSelection.displayName = 'CMultiSelectSelection'
