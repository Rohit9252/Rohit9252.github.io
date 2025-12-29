import * as React from 'react'
import { render } from '@testing-library/react'
import '@testing-library/jest-dom/extend-expect'
import { CBadge, CSmartTable } from '../../../index'
import { Item } from '../types'

test('loads and displays CSpinner component', async () => {
  const columns = [
    {
      key: 'name',
      _style: { width: '20%', color: 'blue' },
      _props: { color: 'primary', className: 'fw-semibold' },
    },
    'registered',
    { key: 'role', filter: false, sorter: false, _style: { width: '20%' } },
    { key: 'status', _style: { width: '20%' } },
    {
      key: 'show_details',
      label: '',
      _style: { width: '1%' },
      filter: false,
      sorter: false,
      _props: { color: 'primary', className: 'fw-semibold' },
    },
  ]
  const usersData = [
    { id: 0, name: 'John Doe', registered: '2022/01/01', role: 'Guest', status: 'Pending' },
    {
      id: 1,
      name: 'Samppa Nori',
      registered: '2022/01/01',
      role: 'Member',
      status: 'Active',
      _props: { color: 'primary', align: 'middle' },
    },
    {
      id: 2,
      name: 'Estavan Lykos',
      registered: '2022/02/07',
      role: 'Staff',
      status: 'Banned',
      _cellProps: { all: { className: 'fw-semibold' }, name: { color: 'info' } },
    },
    { id: 3, name: 'Chetan Mohamed', registered: '2022/02/07', role: 'Admin', status: 'Inactive' },
    {
      id: 4,
      name: 'Derick Maximinus',
      registered: '2022/03/19',
      role: 'Member',
      status: 'Pending',
    },
    { id: 5, name: 'Friderik Dávid', registered: '2022/01/21', role: 'Staff', status: 'Active' },
    { id: 6, name: 'Yiorgos Avraamu', registered: '2022/01/01', role: 'Member', status: 'Active' },
    {
      id: 7,
      name: 'Avram Tarasios',
      registered: '2022/02/07',
      role: 'Staff',
      status: 'Banned',
      _props: { color: 'warning', align: 'middle' },
    },
    { id: 8, name: 'Quintin Ed', registered: '2022/02/07', role: 'Admin', status: 'Inactive' },
    { id: 9, name: 'Enéas Kwadwo', registered: '2022/03/19', role: 'Member', status: 'Pending' },
    { id: 10, name: 'Agapetus Tadeáš', registered: '2022/01/21', role: 'Staff', status: 'Active' },
    { id: 11, name: 'Carwyn Fachtna', registered: '2022/01/01', role: 'Member', status: 'Active' },
    { id: 12, name: 'Nehemiah Tatius', registered: '2022/02/07', role: 'Staff', status: 'Banned' },
    { id: 13, name: 'Ebbe Gemariah', registered: '2022/02/07', role: 'Admin', status: 'Inactive' },
    {
      id: 14,
      name: 'Eustorgios Amulius',
      registered: '2022/03/19',
      role: 'Member',
      status: 'Pending',
    },
    { id: 15, name: 'Leopold Gáspár', registered: '2022/01/21', role: 'Staff', status: 'Active' },
    { id: 16, name: 'Pompeius René', registered: '2022/01/01', role: 'Member', status: 'Active' },
    { id: 17, name: 'Paĉjo Jadon', registered: '2022/02/07', role: 'Staff', status: 'Banned' },
    {
      id: 18,
      name: 'Micheal Mercurius',
      registered: '2022/02/07',
      role: 'Admin',
      status: 'Inactive',
    },
    {
      id: 19,
      name: 'Ganesha Dubhghall',
      registered: '2022/03/19',
      role: 'Member',
      status: 'Pending',
    },
    { id: 20, name: 'Hiroto Šimun', registered: '2022/01/21', role: 'Staff', status: 'Active' },
    { id: 21, name: 'Vishnu Serghei', registered: '2022/01/01', role: 'Member', status: 'Active' },
    { id: 22, name: 'Zbyněk Phoibos', registered: '2022/02/07', role: 'Staff', status: 'Banned' },
    {
      id: 23,
      name: 'Aulus Agmundr',
      registered: '2022/01/01',
      role: 'Member',
      status: 'Pending',
      _selected: true,
    },
    {
      id: 42,
      name: 'Ford Prefect',
      registered: '2001/05/25',
      role: 'Alien',
      status: "Don't panic!",
    },
  ]
  const getBadge = (status: string) => {
    switch (status) {
      case 'Active':
        return 'success'
      case 'Inactive':
        return 'secondary'
      case 'Pending':
        return 'warning'
      case 'Banned':
        return 'danger'
      default:
        return 'primary'
    }
  }
  const { container } = render(
    <CSmartTable
      activePage={3}
      cleaner
      clickableRows
      columns={columns}
      columnFilter
      columnSorter
      footer
      items={usersData}
      itemsPerPageSelect
      itemsPerPage={5}
      pagination
      scopedColumns={{
        status: (item: Item) => (
          <td>
            <CBadge color={getBadge(item.status)}>{item.status}</CBadge>
          </td>
        ),
      }}
      selectable
      sorterValue={{ column: 'status', state: 'asc' }}
      tableFilter
      tableHeadProps={{
        color: 'danger',
      }}
      tableProps={{
        className: 'add-this-class',
        responsive: true,
        striped: true,
        hover: true,
      }}
    />,
  )
  expect(container).toMatchSnapshot()
})
