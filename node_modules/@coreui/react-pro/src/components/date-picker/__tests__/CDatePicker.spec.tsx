import * as React from 'react'
import { render } from '@testing-library/react'
import '@testing-library/jest-dom/extend-expect'
import { CDatePicker } from '../CDatePicker'

test('loads and displays CDatePicker component', async () => {
  const { container } = render(<CDatePicker />)
  expect(container).toMatchSnapshot()
})
