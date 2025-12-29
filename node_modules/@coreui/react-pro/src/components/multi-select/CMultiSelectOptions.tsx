import React, { forwardRef, HTMLAttributes, ReactNode } from 'react'
import PropTypes from 'prop-types'
import classNames from 'classnames'

import { CElementCover } from '../element-cover'
import { CVirtualScroller } from '../virtual-scroller'

import { getNextSibling, getPreviousSibling } from './utils'
import type { Option, OptionsGroup } from './types'

export interface CMultiSelectOptionsProps extends HTMLAttributes<HTMLDivElement> {
  handleOptionOnClick?: (option: Option) => void
  loading?: boolean
  options: (Option | OptionsGroup)[]
  optionsMaxHeight?: number | string
  optionsStyle?: 'checkbox' | 'text'
  optionsTemplate?: (option: Option) => ReactNode
  optionsGroupsTemplate?: (option: OptionsGroup) => ReactNode
  searchNoResultsLabel?: string | ReactNode
  selected: Option[]
  virtualScroller?: boolean
  visibleItems?: number
}

export const CMultiSelectOptions = forwardRef<HTMLDivElement, CMultiSelectOptionsProps>(
  (
    {
      handleOptionOnClick,
      loading,
      options,
      optionsMaxHeight,
      optionsStyle,
      optionsTemplate,
      optionsGroupsTemplate,
      searchNoResultsLabel,
      selected,
      virtualScroller,
      visibleItems = 10,
    },
    ref,
  ) => {
    const handleKeyDown = (event: React.KeyboardEvent<HTMLDivElement>, option: Option) => {
      if (event.code === 'Space' || event.key === 'Enter') {
        event.preventDefault()
        handleOptionOnClick && handleOptionOnClick(option)
      }

      if (event.key === 'Down' || event.key === 'ArrowDown') {
        event.preventDefault()
        const target = event.target as HTMLElement
        const next = getNextSibling(target, '.form-multi-select-option')

        next && (next as HTMLElement).focus()
      }

      if (event.key === 'Up' || event.key === 'ArrowUp') {
        event.preventDefault()
        const target = event.target as HTMLElement
        const prev = getPreviousSibling(target, '.form-multi-select-option')

        prev && (prev as HTMLElement).focus()
      }
    }

    const createOptions = (options: (Option | OptionsGroup)[]): JSX.Element | JSX.Element[] =>
      options.length > 0 ? (
        options.map((option: Option | OptionsGroup, index: number) =>
          'value' in option ? (
            <div
              className={classNames('form-multi-select-option', {
                'form-multi-select-option-with-checkbox': optionsStyle === 'checkbox',
                'form-multi-selected': selected.some((_option) => _option.value === option.value),
                disabled: option.disabled,
              })}
              key={index}
              onClick={() => handleOptionOnClick && handleOptionOnClick(option as Option)}
              onKeyDown={(event) => handleKeyDown(event, option as Option)}
              tabIndex={0}
            >
              {optionsTemplate ? optionsTemplate(option as Option) : option.text}
            </div>
          ) : (
            <div className="form-multi-select-optgroup-label" key={index}>
              {optionsGroupsTemplate ? optionsGroupsTemplate(option as OptionsGroup) : option.label}
            </div>
          ),
        )
      ) : (
        <div className="form-multi-select-options-empty">{searchNoResultsLabel}</div>
      )

    return (
      <>
        {virtualScroller ? (
          <CVirtualScroller
            className="form-multi-select-options"
            visibleItems={visibleItems}
            ref={ref}
          >
            {createOptions(options)}
          </CVirtualScroller>
        ) : (
          <div
            className="form-multi-select-options"
            {...(optionsMaxHeight !== 'auto' && {
              style: { maxHeight: optionsMaxHeight, overflow: 'scroll' },
            })}
            ref={ref}
          >
            {createOptions(options)}
          </div>
        )}
        {loading && <CElementCover />}
      </>
    )
  },
)

CMultiSelectOptions.propTypes = {
  handleOptionOnClick: PropTypes.func,
  loading: PropTypes.bool,
  options: PropTypes.array.isRequired,
  optionsMaxHeight: PropTypes.oneOfType([PropTypes.number, PropTypes.string]),
  optionsStyle: PropTypes.oneOf(['checkbox', 'text']),
  optionsTemplate: PropTypes.func,
  optionsGroupsTemplate: PropTypes.func,
  searchNoResultsLabel: PropTypes.oneOfType([PropTypes.string, PropTypes.node]),
  virtualScroller: PropTypes.bool,
  visibleItems: PropTypes.number,
}

CMultiSelectOptions.displayName = 'CMultiSelectOptions'
