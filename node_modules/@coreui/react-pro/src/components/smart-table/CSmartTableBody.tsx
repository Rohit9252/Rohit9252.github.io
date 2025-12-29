import React, { forwardRef, MouseEvent, ReactNode } from 'react'
import PropTypes from 'prop-types'

import { CTableBody, CTableBodyProps } from '../table/CTableBody'
import { CFormCheck } from '../form'
import { CTableDataCell, CTableRow } from '../table'

import { isObjectInArray } from '../../utils'

import type { Item, ScopedColumns } from './types'
import { getClickedColumnName, getTableDataCellProps } from './utils'

export interface CSmartTableBodyProps extends CTableBodyProps {
  clickableRows?: boolean
  columnNames: string[]
  currentItems: Item[]
  firstItemOnActivePageIndex: number
  noItemsLabel?: string | ReactNode
  onRowChecked?: (item: Item, value: boolean) => void
  onRowClick?: (item: Item, index: number, columnName: string, event: MouseEvent | boolean) => void
  scopedColumns?: ScopedColumns
  selectable?: boolean
  selected?: Item[]
}

export const CSmartTableBody = forwardRef<HTMLTableSectionElement, CSmartTableBodyProps>(
  (
    {
      clickableRows,
      columnNames,
      currentItems,
      firstItemOnActivePageIndex,
      noItemsLabel,
      onRowChecked,
      onRowClick,
      scopedColumns,
      selectable,
      selected,
      ...rest
    },
    ref,
  ) => {
    const colspan: number = selectable ? columnNames.length + 1 : columnNames.length

    return (
      <CTableBody
        {...(clickableRows && {
          style: { cursor: 'pointer' },
        })}
        {...rest}
        ref={ref}
      >
        {currentItems.length > 0 ? (
          currentItems.map((item: Item, trIndex) => {
            return (
              <React.Fragment key={trIndex}>
                <CTableRow
                  {...(item._props && { ...item._props })}
                  {...(clickableRows && { tabIndex: 0 })}
                  onClick={(event) =>
                    onRowClick &&
                    onRowClick(
                      item,
                      trIndex + firstItemOnActivePageIndex,
                      getClickedColumnName(event.target as HTMLTextAreaElement, columnNames),
                      event,
                    )
                  }
                >
                  {selectable && (
                    <CTableDataCell>
                      <CFormCheck
                        checked={
                          selected &&
                          isObjectInArray(selected, item, ['_cellProps', '_props', '_selected'])
                        }
                        onChange={(event) => {
                          const _item = { ...item }
                          delete _item['_cellProps']
                          delete _item['_props']
                          delete _item['_selected']
                          onRowChecked && onRowChecked(_item, event.target.checked)
                        }}
                      />
                    </CTableDataCell>
                  )}
                  {columnNames.map((colName, index) => {
                    return (
                      (scopedColumns &&
                        scopedColumns[colName] &&
                        React.cloneElement(
                          scopedColumns[colName](item, trIndex + firstItemOnActivePageIndex),
                          {
                            key: index,
                          },
                        )) ||
                      (item[colName] !== undefined && (
                        <CTableDataCell {...getTableDataCellProps(item, colName)} key={index}>
                          {item[colName]}
                        </CTableDataCell>
                      ))
                    )
                  })}
                </CTableRow>
                {scopedColumns && scopedColumns.details && (
                  <>
                    <CTableRow>
                      <CTableDataCell
                        colSpan={colspan}
                        className="p-0"
                        style={{ borderBottomWidth: 0 }}
                        tabIndex={-1}
                      ></CTableDataCell>
                    </CTableRow>
                    <CTableRow
                      onClick={(event) =>
                        onRowClick &&
                        onRowClick(
                          item,
                          trIndex + firstItemOnActivePageIndex,
                          getClickedColumnName(event.target as HTMLTextAreaElement, columnNames),
                          true,
                        )
                      }
                      className="p-0"
                      key={`details${trIndex}`}
                    >
                      <CTableDataCell colSpan={colspan} className="p-0" style={{ border: 0 }}>
                        {scopedColumns.details(item, trIndex + firstItemOnActivePageIndex)}
                      </CTableDataCell>
                    </CTableRow>
                  </>
                )}
              </React.Fragment>
            )
          })
        ) : (
          <CTableRow>
            <CTableDataCell colSpan={colspan}>{noItemsLabel}</CTableDataCell>
          </CTableRow>
        )}
      </CTableBody>
    )
  },
)

CSmartTableBody.propTypes = {
  clickableRows: PropTypes.bool,
  currentItems: PropTypes.array.isRequired,
  firstItemOnActivePageIndex: PropTypes.number.isRequired,
  noItemsLabel: PropTypes.oneOfType([PropTypes.string, PropTypes.node]),
  onRowChecked: PropTypes.func,
  onRowClick: PropTypes.func,
  columnNames: PropTypes.array.isRequired,
  scopedColumns: PropTypes.object,
  selectable: PropTypes.bool,
  selected: PropTypes.array,
}

CSmartTableBody.displayName = 'CSmartTableBody'
