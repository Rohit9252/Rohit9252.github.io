import * as React from 'react'
import { render } from '@testing-library/react'
import '@testing-library/jest-dom/extend-expect'
import { CCalendar } from '../CCalendar'

test('loads and displays CCalendar component', async () => {
  const { container } = render(<CCalendar />)
  expect(container).toMatchSnapshot()
})
