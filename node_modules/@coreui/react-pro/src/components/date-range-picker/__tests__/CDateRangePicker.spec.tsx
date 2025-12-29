import * as React from 'react'
import { render } from '@testing-library/react'
import '@testing-library/jest-dom/extend-expect'
import { CDateRangePicker } from '../CDateRangePicker'

test('loads and displays CDateRangePicker component', async () => {
  const { container } = render(<CDateRangePicker />)
  expect(container).toMatchSnapshot()
})
