import { HTMLAttributes, MouseEvent, ReactNode } from 'react'

import { CSmartPaginationProps } from '../smart-pagination/CSmartPagination'
import { CTableProps } from '../table/CTable'
import { CTableBodyProps } from '../table/CTableBody'
import { CTableFootProps } from '../table/CTableFoot'
import { CTableHeadProps } from '../table/CTableHead'

import type {
  Column,
  ColumnFilter,
  ColumnFilterValue,
  FooterItem,
  Item,
  ItemsPerPageSelect,
  Pagination,
  Sorter,
  ScopedColumns,
  SorterValue,
  TableFilter,
} from './types'

export interface CSmartTableProps extends HTMLAttributes<HTMLDivElement> {
  /**
   * Sets active page. If 'pagination' prop is enabled, activePage is set only initially.
   */
  activePage?: number
  /**
   * When set, displays table cleaner above table, next to the table filter (or in place of table filter if `tableFilter` prop is not set)
   * Cleaner resets `tableFilterValue`, `columnFilterValue`, `sorterValue`. If clean is possible it is clickable (`tabIndex="0"` `role="button"`, `color="danger"`), otherwise it is not clickable and transparent. Cleaner can be customized through the `cleaner` slot.
   */
  cleaner?: boolean
  /**
   * Style table items as clickable.
   */
  clickableRows?: boolean
  /**
   * When set, displays additional filter row between table header and items, allowing filtering by specific column.
   * Column filter can be customized, by passing prop as object with additional options as keys. Available options:
   * - external (Boolean) - Disables automatic filtering inside component.
   * - lazy (Boolean) - Set to true to trigger filter updates only on change event.
   */
  columnFilter?: boolean | ColumnFilter
  /**
   * Value of table filter. To set pass object where keys are column names and values are filter strings e.g.:
   * `{ user: 'John', age: 12 }`
   */
  columnFilterValue?: ColumnFilterValue
  /**
   * Prop for table columns configuration. If prop is not defined, table will display columns based on the first item keys, omitting keys that begins with underscore (e.g. '_classes')
   *
   * In columns prop each array item represents one column. Item might be specified in two ways:
   * String: each item define column name equal to item value.
   * Object: item is object with following keys available as column configuration:
   * - key (required)(String) - define column name equal to item key.
   * - label (String) - define visible label of column. If not defined, label will be generated automatically based on column name, by converting kebab-case and snake_case to individual words and capitalization of each word.
   * - _classes (String/Array/Object) - adds classes to all cels in column
   * - _style (String/Array/Object) - adds styles to the column header (useful for defining widths)
   * - sorter (Boolean) - disables sorting of the column when set to false
   * - filter (Boolean) - removes filter from column when set to false.
   */
  columns?: (string | Column)[]
  /**
   * Enables table sorting by column value. Sorting will be performed corectly only if values in column are of one type: string (case insensitive) or number.
   *
   * Sorter can be customized, by passing prop as object with additional options as keys. Available options:
   * - external (Boolean) - Disables automatic sorting inside component.
   * - resetable (Boolean) - If set to true clicking on sorter have three states: ascending, descending and null. That means that third click on sorter will reset sorting, and restore table to original order.
   */
  columnSorter?: boolean | Sorter
  /**
   * ReactNode for passing custom CElementCover content.
   *
   * @since 4.9.0
   */
  elementCover?: ReactNode
  /**
   * If `true` Displays table footer, which mirrors table header. (without column filter).
   * Or Array of objects or strings, where each element represents one cell in the table footer.
   *
   * Example items:
   * `['FooterCell', 'FooterCell', 'FooterCell']`
   * or
   * `[{ label: 'FooterCell', _props: { color: 'success' }, ...]`
   */
  footer?: boolean | (FooterItem | string)[]
  /**
   * Set to false to remove table header.
   */
  header?: boolean
  /**
   * Array of objects, where each object represents one item - row in table. Additionally, you can add style classes to each row by passing them by '_props' key and to single cell by '_cellProps'.
   *
   * Example item:
   * `{ name: 'John' , age: 12, _props: { color: 'success' }, _cellProps: { age: { className: 'fw-bold'}}}`
   *
   * @since 4.9.0
   */
  items?: Item[]
  /**
   * The total number of items. Use if you pass a portion of data from an external source to let know component what is the total number of items.
   */
  itemsNumber?: number
  /**
   * Number of items per site, when pagination is enabled.
   */
  itemsPerPage?: number
  /**
   * Label for items per page selector.
   */
  itemsPerPageLabel?: string
  /**
   * Items per page selector options.
   */
  itemsPerPageOptions?: number[]
  /**
   * Adds select element over table, which is used for control items per page in pagination. If you want to customize this element, pass object with optional values:
   * - label (String) - replaces default label text
   * - values (Array) - custom array of pagination values
   * - external (Boolean) - disables automatic 'itemsPerPage' change (use to change pages externaly by 'pagination-change' event).
   */
  itemsPerPageSelect?: boolean | ItemsPerPageSelect
  /**
   * When set, table will have loading style: loading spinner and reduced opacity.
   */
  loading?: boolean
  /**
   * ReactNode or string for passing custom noItemsLabel texts.
   */
  noItemsLabel?: string | ReactNode
  /**
   * Page change callback.
   */
  onActivePageChange?: (value: number) => void
  /**
   * Column filter change callback.
   */
  onColumnFilterChange?: (value: ColumnFilterValue) => void //!
  /**
   * Filtered items change callback.
   */
  onFilteredItemsChange?: (items: Item[]) => void
  /**
   * Pagination change callback.
   */
  onItemsPerPageChange?: (value: number) => void
  /**
   * Row click callback.
   */
  onRowClick?: (item: Item, index: number, columnName: string, event: MouseEvent | boolean) => void
  /**
   * Select all callback.
   *
   * @since 4.9.0
   */
  onSelectAll?: () => void
  /**
   * Selected items change callback.
   */
  onSelectedItemsChange?: (items: Item[]) => void
  /**
   * Sorter value change callback.
   */
  onSorterChange?: (value: SorterValue) => void
  /**
   * Table filter change callback.
   */
  onTableFilterChange?: (value?: string) => void
  /**
   * Enables default pagination. Set to true for default setup or pass an object with additional CPagination props. Default pagination will always have the computed number of pages that cannot be changed. The number of pages is generated based on the number of passed items and 'itemsPerPage' prop. If this restriction is an obstacle, you can make external CPagination instead.
   */
  pagination?: boolean | Pagination
  /**
   * Properties to `CSmartPagination` component - https://coreui.io/react/docs/components/smart-pagination#csmartpagination
   */
  paginationProps?: CSmartPaginationProps
  /**
   * Scoped columns.
   */
  scopedColumns?: ScopedColumns
  /**
   * Add checkboxes to make table rows selectable.
   */
  selectable?: boolean
  /**
   * Enables select all checkbox displayed in the header of the table.
   *
   * Can be customized, by passing prop as object with additional options as keys. Available options:
   * - external (Boolean) - Disables automatic selection inside the component.
   *
   * @since 4.9.0
   */
  selectAll?: boolean | { external?: boolean }
  /**
   * Array of selected objects, where each object represents one item - row in table.
   *
   * Example item: `{ name: 'John' , age: 12 }`
   *
   * @since 4.9.0
   */
  selected?: Item[]
  /**
   * State of the sorter. Name key is column name, direction can be 'asc' or 'desc'.
   */
  sorterValue?: SorterValue
  /**
   * Sorter icon when items are unsorted.
   */
  sortingIcon?: ReactNode
  /**
   * Sorter icon when items are sorted ascending.
   */
  sortingIconAscending?: ReactNode
  /**
   * Sorter icon when items are sorted descending.
   */
  sortingIconDescending?: ReactNode
  /**
   * Properties to `CTableBody` component - https://coreui.io/react/docs/components/table/#ctablebody
   */
  tableBodyProps?: CTableBodyProps
  /**
   * Properties to `CTableFoot` component - https://coreui.io/react/docs/components/table/#ctablefoot
   */
  tableFootProps?: CTableFootProps
  /**
   * When set, displays table filter above table, allowing filtering by specific column.
   *
   * Column filter can be customized, by passing prop as object with additional options as keys. Available options:
   * - external (Boolean) - Disables automatic filtering inside component.
   * - lazy (Boolean) - Set to true to trigger filter updates only on change event.
   */
  tableFilter?: boolean | TableFilter
  /**
   * The element represents a caption for a component.
   */
  tableFilterLabel?: string
  /**
   * Specifies a short hint that is visible in the search input.
   */
  tableFilterPlaceholder?: string
  /**
   * Value of table filter.
   */
  tableFilterValue?: string
  /**
   * Properties to `CTableHead` component - https://coreui.io/react/docs/components/table/#ctablehead
   */
  tableHeadProps?: CTableHeadProps
  /**
   * Properties to `CTable` component - https://coreui.io/react/docs/components/table/#ctable
   */
  tableProps?: CTableProps
}
