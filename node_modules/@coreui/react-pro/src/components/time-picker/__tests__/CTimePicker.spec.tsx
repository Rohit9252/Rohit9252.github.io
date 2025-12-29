import * as React from 'react'
import { render } from '@testing-library/react'
import '@testing-library/jest-dom/extend-expect'
import { CTimePicker } from '../CTimePicker'

test('loads and displays CTimePicker component', async () => {
  const { container } = render(<CTimePicker />)
  expect(container).toMatchSnapshot()
})
