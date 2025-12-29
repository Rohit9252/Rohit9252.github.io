import React, { forwardRef, InputHTMLAttributes } from 'react'
import PropTypes from 'prop-types'

import type { Option } from './types'

export interface CMultiSelectNativeSelectProps
  extends Omit<InputHTMLAttributes<HTMLSelectElement>, 'options'> {
  options?: Option[]
  value?: string | number | string[]
}

const createNativeOptions = (options: Option[]) =>
  options &&
  options.map((option: Option, index: number) =>
    option.options ? (
      <optgroup label={option.label} key={index}>
        {createNativeOptions(option.options)}
      </optgroup>
    ) : (
      <option value={option.value} key={index} disabled={option.disabled}>
        {option.text}
      </option>
    ),
  )

export const CMultiSelectNativeSelect = forwardRef<
  HTMLSelectElement,
  CMultiSelectNativeSelectProps
>(({ id, options, ...rest }, ref) => {
  return (
    <select
      className="multi-select-new"
      {...(id && { id: `${id}-multi-select` })}
      {...(id && { name: `${id}-multi-select` })}
      tabIndex={-1}
      style={{ display: 'none' }}
      {...rest}
      ref={ref}
    >
      {options && createNativeOptions(options)}
    </select>
  )
})

CMultiSelectNativeSelect.propTypes = {
  options: PropTypes.array,
  value: PropTypes.oneOfType([
    PropTypes.number,
    PropTypes.string,
    PropTypes.arrayOf(PropTypes.string.isRequired),
  ]),
}

CMultiSelectNativeSelect.displayName = 'CMultiSelectNativeSelect'
