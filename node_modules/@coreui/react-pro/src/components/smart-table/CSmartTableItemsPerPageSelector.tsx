import React, { forwardRef, HTMLAttributes } from 'react'
import PropTypes from 'prop-types'

import { CFormLabel, CFormSelect } from '../form/'

interface CSmartTableItemsPerPageSelectorProps extends HTMLAttributes<HTMLSelectElement> {
  itemsPerPage?: number
  itemsPerPageLabel?: string
  itemsPerPageOptions?: number[]
}

export const CSmartTableItemsPerPageSelector = forwardRef<
  HTMLSelectElement,
  CSmartTableItemsPerPageSelectorProps
>(({ itemsPerPage, itemsPerPageLabel, itemsPerPageOptions, ...rest }, ref) => {
  return (
    <div className="row">
      <CFormLabel className="col-auto col-form-label">{itemsPerPageLabel}</CFormLabel>
      <div className="col-auto">
        <CFormSelect defaultValue={itemsPerPage} {...rest} ref={ref}>
          {itemsPerPageOptions &&
            itemsPerPageOptions.map((number, index) => {
              return (
                <option value={number} key={index}>
                  {number}
                </option>
              )
            })}
        </CFormSelect>
      </div>
    </div>
  )
})

CSmartTableItemsPerPageSelector.propTypes = {
  itemsPerPage: PropTypes.number,
  itemsPerPageLabel: PropTypes.string,
  itemsPerPageOptions: PropTypes.array,
}

CSmartTableItemsPerPageSelector.displayName = 'CSmartTableItemsPerPageSelector'
