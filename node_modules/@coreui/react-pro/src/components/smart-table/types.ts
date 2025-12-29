import { ReactNode } from 'react'

import { CTableDataCellProps } from '../table/CTableDataCell'
import { CTableHeaderCellProps } from '../table/CTableHeaderCell'
import { CTableRowProps } from '../table/CTableRow'

export type Column = {
  children?: Column[]
  filter?: boolean | ((values: any[], onChange: (value: any) => void) => ReactNode)
  group?: string
  key: string
  label?: string
  sorter?: boolean
  _style?: any
  _props?: CTableHeaderCellProps
}

export type ColumnFilter = {
  lazy?: boolean
  external?: boolean
}

export type ColumnFilterValue = {
  [key: string]: any
}

export type FooterItem = {
  label?: string
  _props?: CTableDataCellProps
}

export type Group = {
  children?: Group[] | Column[]
  colspan?: number
  deep?: number
  group?: string
  key: string
  label?: string
  _style?: any
  _props?: CTableHeaderCellProps
}

export type Item = {
  [key: string]: number | string | any
  _cellProps?: any
  _props?: CTableRowProps
  _selected?: boolean
}

export type ItemsPerPageSelect = {
  external?: boolean
  label?: string
  values?: Array<number>
}

export type Pagination = {
  external?: boolean
}

export type Sorter = {
  resetable?: boolean
  external?: boolean
}

export type ScopedColumns = {
  [key: string]: any
  details?: (a: Item, b: number) => ReactNode
}

export type SorterValue = {
  column?: string
  state?: number | string
}

export type TableFilter = {
  lazy?: boolean
  external?: boolean
}
