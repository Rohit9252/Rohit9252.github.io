import React, { ChangeEvent, forwardRef, useEffect, useMemo, useRef, useState } from 'react'
import PropTypes from 'prop-types'

import { cilArrowBottom, cilArrowTop, cilFilterX, cilSwapVertical } from '@coreui/icons'
import CIcon from '@coreui/icons-react'

import { CElementCover } from '../element-cover'
import { CFormInput, CFormLabel, CFormSelect } from '../form'
import { CSmartPagination } from '../smart-pagination'
import { CTable, CTableDataCell, CTableFoot, CTableRow } from '../table'

import { CSmartTableBody } from './CSmartTableBody'
import { CSmartTableHead } from './CSmartTableHead'
import { CSmartTableProps } from './CSmartTableInterface'

import { isObjectInArray } from '../../utils'

import type { ColumnFilterValue, FooterItem, Item, SorterValue } from './types'
import {
  filterColumns,
  filterTable,
  getColumnNames,
  getColumnNamesFromItems,
  isSortable,
  sortItems,
} from './utils'

export const CSmartTable = forwardRef<HTMLDivElement, CSmartTableProps>(
  (
    {
      activePage = 1,
      cleaner,
      clickableRows,
      columnFilter,
      columnFilterValue, // TODO: consider to use only columnFilter prop
      columns,
      columnSorter,
      elementCover,
      footer,
      header = true,
      items,
      itemsNumber,
      itemsPerPage = 10,
      itemsPerPageLabel = 'Items per page:',
      itemsPerPageOptions = [5, 10, 20, 50],
      itemsPerPageSelect,
      loading,
      noItemsLabel = 'No items found',
      onActivePageChange,
      onColumnFilterChange,
      onFilteredItemsChange,
      onItemsPerPageChange,
      onRowClick,
      onSelectAll,
      onSelectedItemsChange,
      onSorterChange,
      onTableFilterChange,
      pagination,
      paginationProps,
      scopedColumns,
      selected,
      selectable,
      selectAll = true,
      sorterValue,
      sortingIcon = <CIcon width={18} icon={cilSwapVertical} key="csv" />,
      sortingIconAscending = <CIcon width={18} icon={cilArrowTop} key="cat" />,
      sortingIconDescending = <CIcon width={18} icon={cilArrowBottom} key="cab" />,
      tableBodyProps,
      tableFootProps,
      tableFilter,
      tableFilterLabel = 'Filter:',
      tableFilterPlaceholder = 'type string...',
      tableFilterValue, // TODO: consider to use only tableFilter prop
      tableHeadProps,
      tableProps,
      ...rest
    },
    ref,
  ) => {
    const mountedRef = useRef(false)
    const [_activePage, setActivePage] = useState(activePage)
    const [_items, setItems] = useState<Item[]>([])
    const [_itemsNumber, setItemsNumber] = useState(itemsNumber)
    const [_itemsPerPage, setItemsPerPage] = useState(itemsPerPage)
    const [_selected, setSelected] = useState<Item[]>([])
    const [columnFilterState, setColumnFilterState] = useState<ColumnFilterValue>({})
    const [selectedAll, setSelectedAll] = useState<boolean | string>()
    const [sorterState, setSorterState] = useState<SorterValue>({})
    const [tableFilterState, setTableFilterState] = useState<string>(tableFilterValue ?? '')

    useEffect(() => {
      setActivePage(activePage)
    }, [activePage])

    useEffect(() => {
      if (items && items.length < _itemsPerPage * _activePage - _itemsPerPage) {
        setActivePage(1)
      }

      const selected: Item[] = []

      items &&
        items.forEach((item: Item) => {
          if (item._selected) {
            const _item = { ...item }
            delete _item['_cellProps']
            delete _item['_props']
            delete _item['_selected']
            selected.push(_item)
          }
        })

      if (selected.length > 0) {
        setSelected([..._selected, ...selected])
      }

      if (Array.isArray(items)) {
        setItems(items)
        // eslint-disable-next-line unicorn/explicit-length-check
        setItemsNumber(itemsNumber || items.length)
      }
    }, [JSON.stringify(items)])

    useEffect(() => {
      Array.isArray(selected) && setSelected(selected)
    }, [JSON.stringify(selected)])

    useEffect(() => {
      itemsNumber && setItemsNumber(itemsNumber)
    }, [itemsNumber])

    useEffect(() => {
      columnFilterValue && setColumnFilterState(columnFilterValue)
    }, [JSON.stringify(columnFilterValue)])

    useEffect(() => {
      setSorterState({ ...sorterValue })
    }, [JSON.stringify(sorterValue)])

    useEffect(() => setItemsPerPage(itemsPerPage), [itemsPerPage])

    useEffect(() => {
      mountedRef.current && onActivePageChange && onActivePageChange(_activePage)
    }, [_activePage])

    useEffect(() => {
      mountedRef.current && onItemsPerPageChange && onItemsPerPageChange(_itemsPerPage)
      itemsPerPage !== _itemsPerPage && setActivePage(1) // TODO: set proper page after _itemsPerPage update
    }, [_itemsPerPage])

    useEffect(() => {
      mountedRef.current && sorterState && onSorterChange && onSorterChange(sorterState)
    }, [JSON.stringify(sorterState)])

    useEffect(() => {
      mountedRef.current && onColumnFilterChange && onColumnFilterChange(columnFilterState)
    }, [columnFilterState])

    useEffect(() => {
      mountedRef.current && onTableFilterChange && onTableFilterChange(tableFilterState)
    }, [tableFilterState])

    useEffect(() => {
      if (selectable) {
        onSelectedItemsChange && onSelectedItemsChange(_selected)
        if (_selected.length === _itemsNumber) {
          setSelectedAll(true)
          return
        }

        if (_selected.length === 0) {
          setSelectedAll(false)
          return
        }

        if (_selected.length > 0 && _selected.length !== _itemsNumber) {
          setSelectedAll('indeterminate')
        }
      }
    }, [JSON.stringify(_selected), _itemsNumber])

    const columnNames = useMemo(() => getColumnNames(columns, _items), [columns, _items])

    const itemsDataColumns = useMemo(
      () => columnNames.filter((name) => getColumnNamesFromItems(_items).includes(name)),
      [columnNames, _items],
    )

    const filteredColumns: Item[] = useMemo(
      () => filterColumns(_items, columnFilter, columnFilterState, itemsDataColumns),
      [columnFilterState, JSON.stringify(_items)],
    )

    const filteredTable: Item[] = useMemo(
      () => filterTable(filteredColumns, tableFilter, tableFilterState, itemsDataColumns),
      [tableFilterState, JSON.stringify(tableFilterValue), JSON.stringify(filteredColumns)],
    )

    const sortedItems: Item[] = useMemo(
      () => sortItems(columnSorter, filteredTable, itemsDataColumns, sorterState),
      [
        JSON.stringify(filteredTable),
        JSON.stringify(sorterState),
        JSON.stringify(columnSorter),
        JSON.stringify(filteredColumns),
        JSON.stringify(_items),
      ],
    )

    const numberOfPages: number = _itemsPerPage ? Math.ceil(sortedItems.length / _itemsPerPage) : 1

    const firstItemOnActivePageIndex: number = _activePage ? (_activePage - 1) * _itemsPerPage : 0

    const currentItems: Item[] = _activePage
      ? sortedItems.slice(firstItemOnActivePageIndex, firstItemOnActivePageIndex + _itemsPerPage)
      : sortedItems

    useEffect(() => {
      mountedRef.current && onFilteredItemsChange && onFilteredItemsChange(sortedItems)
    }, [JSON.stringify(sortedItems)])

    const handleClean = (): void => {
      setTableFilterState('')
      setColumnFilterState({})
      setSorterState({})
    }

    const handleColumnFilterChange = (colName: string, value: any, type?: string): void => {
      const isLazy = columnFilter && typeof columnFilter === 'object' && columnFilter.lazy === true
      if ((isLazy && type === 'input') || (!isLazy && type === 'change')) {
        return
      }

      const newState = { ...columnFilterState, [`${colName}`]: value }
      setActivePage(1)
      setColumnFilterState(newState)
    }

    const handleItemsPerPageChange = (event: ChangeEvent<HTMLSelectElement>): void => {
      if (
        typeof itemsPerPageSelect !== 'object' ||
        (typeof itemsPerPageSelect === 'object' && !itemsPerPageSelect.external)
      ) {
        setItemsPerPage(Number((event.target as HTMLSelectElement).value))
      }
    }

    const handleRowChecked = (item: Item, value: boolean) => {
      if (value && !isObjectInArray(_selected, item, ['_cellProps', '_props', '_selected'])) {
        setSelected([..._selected, item])
        return
      }

      setSelected(
        _selected.filter(
          (_item: Item) => !isObjectInArray([_item], item, ['_cellProps', '_props', '_selected']),
        ),
      )
    }

    const handleSelectAllChecked = () => {
      if (selectedAll === true) {
        setSelected([])
        return
      }

      onSelectAll && onSelectAll()

      if (selectAll && typeof selectAll === 'object' && selectAll.external) {
        return
      }

      const selected = _items.map((item) => {
        return { ...item }
      })

      setSelected(
        selected.map((item) => {
          delete item['_cellProps']
          delete item['_props']
          delete item['_selected']

          return item
        }),
      )
    }

    const handleSorterChange = (column: string, index: number): void => {
      if (!isSortable(index, columns, columnSorter, itemsDataColumns, columnNames)) {
        return
      }

      //if column changed or sort was descending change asc to true
      const state = sorterState ?? { column: '', state: '' }

      if (state.column === column) {
        if (state.state === 0) {
          state.state = 'asc'
        } else if (state.state === 'asc') {
          state.state = 'desc'
        } else {
          state.state = typeof columnSorter === 'object' && !columnSorter.resetable ? 'asc' : 0
        }
      } else {
        state.column = column
        state.state = 'asc'
      }

      setSorterState({ ...state })
    }

    const handleTableFilterChange = (value: string, type: string): void => {
      const isLazy = tableFilter && typeof tableFilter === 'object' && tableFilter.lazy === true
      if ((isLazy && type === 'input') || (!isLazy && type === 'change')) {
        return
      }

      setActivePage(1)
      setTableFilterState(value)
    }

    useEffect(() => {
      mountedRef.current = true
    }, [])

    return (
      <>
        <div {...rest} ref={ref}>
          {(itemsPerPageSelect || tableFilter || cleaner) && (
            <div className="row my-2 mx-0">
              {(tableFilter || cleaner) && (
                <>
                  <div className="col-auto p-0">
                    {tableFilter && (
                      <div className="row mb-2">
                        <CFormLabel className="col-sm-auto col-form-label">
                          {tableFilterLabel}
                        </CFormLabel>
                        <div className="col-sm-auto">
                          <CFormInput
                            onInput={(e) => {
                              handleTableFilterChange((e.target as HTMLInputElement).value, 'input')
                            }}
                            onChange={(e) => {
                              handleTableFilterChange(
                                (e.target as HTMLInputElement).value,
                                'change',
                              )
                            }}
                            placeholder={tableFilterPlaceholder}
                            value={tableFilterState || ''}
                          />
                        </div>
                      </div>
                    )}
                  </div>
                  <div className="col-auto p-0">
                    {cleaner && (
                      <button
                        type="button"
                        className="btn btn-transparent"
                        {...(!(
                          tableFilterState ||
                          sorterState?.column ||
                          Object.values(columnFilterState).join('')
                        ) && {
                          disabled: true,
                          tabIndex: -1,
                        })}
                        onClick={() => handleClean()}
                        onKeyDown={(event) => {
                          if (event.key === 'Enter') handleClean()
                        }}
                      >
                        <CIcon width={18} icon={cilFilterX} />
                      </button>
                    )}
                  </div>
                </>
              )}
            </div>
          )}
        </div>
        <div className="position-relative">
          <CTable {...tableProps}>
            {header && (
              <CSmartTableHead
                {...tableHeadProps}
                columnFilter={columnFilter}
                columnFilterState={columnFilterState}
                columns={columns ?? columnNames}
                columnSorter={columnSorter}
                items={_items}
                selectable={selectable}
                selectAll={selectAll}
                selectedAll={selectedAll}
                sorterState={sorterState}
                sortingIcon={sortingIcon}
                sortingIconAscending={sortingIconAscending}
                sortingIconDescending={sortingIconDescending}
                handleFilterOnChange={(key, event) =>
                  handleColumnFilterChange(key, event, 'change')
                }
                handleFilterOnInput={(key, event) => handleColumnFilterChange(key, event, 'input')}
                handleOnCustomFilterChange={(key, event) => handleColumnFilterChange(key, event)}
                handleSelectAllChecked={() => handleSelectAllChecked()}
                handleSort={(key, index) => handleSorterChange(key, index)}
              />
            )}
            <CSmartTableBody
              clickableRows={clickableRows}
              currentItems={currentItems}
              firstItemOnActivePageIndex={firstItemOnActivePageIndex}
              noItemsLabel={noItemsLabel}
              onRowClick={(item, index, columnName, event) =>
                clickableRows && onRowClick && onRowClick(item, index, columnName, event)
              }
              onRowChecked={(item, value) => handleRowChecked(item, value)}
              columnNames={columnNames}
              scopedColumns={scopedColumns}
              selectable={selectable}
              selected={_selected}
              {...tableBodyProps}
            />
            {typeof footer === 'boolean' && footer && (
              <CSmartTableHead
                component={CTableFoot}
                {...tableFootProps}
                columnFilter={false}
                columnSorter={false}
                columns={columns ?? columnNames}
                items={_items}
                handleSelectAllChecked={() => handleSelectAllChecked()}
                selectable={selectable}
                selectAll={selectAll}
                selectedAll={selectedAll}
                showGroups={false}
              />
            )}
            {Array.isArray(footer) && (
              <CTableFoot {...tableFootProps}>
                <CTableRow>
                  {footer.map((item: FooterItem | string, index: number) => (
                    <CTableDataCell
                      {...(typeof item === 'object' && item._props && { ...item._props })}
                      key={index}
                    >
                      {typeof item === 'object' ? item.label : item}
                    </CTableDataCell>
                  ))}
                </CTableRow>
              </CTableFoot>
            )}
          </CTable>
          {loading && (
            <CElementCover
              boundaries={[
                { sides: ['top'], query: 'tbody' },
                { sides: ['bottom'], query: 'tbody' },
              ]}
            >
              {elementCover}
            </CElementCover>
          )}
        </div>

        {(pagination || itemsPerPageSelect) && (
          <div className="row">
            <div className="col">
              {((pagination && numberOfPages > 1) || (paginationProps && paginationProps.pages > 1)) && (
                <CSmartPagination
                  activePage={_activePage}
                  onActivePageChange={(page) => {
                    pagination && typeof pagination === 'object' && pagination.external
                      ? onActivePageChange && onActivePageChange(page)
                      : setActivePage(page)
                  }}
                  pages={numberOfPages}
                  {...paginationProps}
                />
              )}
            </div>
            <div className="col-auto ms-auto">
              {itemsPerPageSelect && (
                <div className="row">
                  <CFormLabel className="col-auto col-form-label">{itemsPerPageLabel}</CFormLabel>
                  <div className="col-auto">
                    <CFormSelect
                      defaultValue={_itemsPerPage}
                      onChange={(event: ChangeEvent<HTMLSelectElement>) =>
                        handleItemsPerPageChange(event)
                      }
                    >
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
              )}
            </div>
          </div>
        )}
      </>
    )
  },
)

CSmartTable.propTypes = {
  activePage: PropTypes.number,
  cleaner: PropTypes.bool,
  clickableRows: PropTypes.bool,
  columnFilter: PropTypes.oneOfType([PropTypes.bool, PropTypes.object]),
  columnFilterValue: PropTypes.object,
  columns: PropTypes.array,
  columnSorter: PropTypes.oneOfType([PropTypes.bool, PropTypes.object]),
  elementCover: PropTypes.node,
  footer: PropTypes.oneOfType([PropTypes.bool, PropTypes.array]),
  header: PropTypes.bool,
  items: PropTypes.array,
  itemsNumber: PropTypes.number,
  itemsPerPage: PropTypes.number,
  itemsPerPageLabel: PropTypes.string,
  itemsPerPageOptions: PropTypes.array,
  itemsPerPageSelect: PropTypes.oneOfType([PropTypes.bool, PropTypes.object]),
  loading: PropTypes.bool,
  noItemsLabel: PropTypes.oneOfType([PropTypes.string, PropTypes.node]),
  onActivePageChange: PropTypes.func,
  onColumnFilterChange: PropTypes.func,
  onFilteredItemsChange: PropTypes.func,
  onItemsPerPageChange: PropTypes.func,
  onRowClick: PropTypes.func,
  onSelectAll: PropTypes.func,
  onSelectedItemsChange: PropTypes.func,
  onSorterChange: PropTypes.func, // TODO: change to `onColumnSorterChange` in v5
  onTableFilterChange: PropTypes.func,
  pagination: PropTypes.oneOfType([PropTypes.bool, PropTypes.object]),
  paginationProps: PropTypes.any, // TODO: update
  scopedColumns: PropTypes.object,
  selectable: PropTypes.bool,
  selectAll: PropTypes.oneOfType([PropTypes.bool, PropTypes.object]),
  selected: PropTypes.array,
  sorterValue: PropTypes.object,
  sortingIcon: PropTypes.node,
  sortingIconAscending: PropTypes.node,
  sortingIconDescending: PropTypes.node,
  tableBodyProps: PropTypes.object,
  tableFootProps: PropTypes.object,
  tableFilter: PropTypes.oneOfType([PropTypes.bool, PropTypes.object]),
  tableFilterLabel: PropTypes.string,
  tableFilterPlaceholder: PropTypes.string,
  tableFilterValue: PropTypes.string,
  tableHeadProps: PropTypes.object,
  tableProps: PropTypes.object,
}

CSmartTable.displayName = 'CSmartTable'
