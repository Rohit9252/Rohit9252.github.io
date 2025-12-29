import * as React from 'react'
import { render } from '@testing-library/react'
import '@testing-library/jest-dom/extend-expect'
import { CPicker } from '../CPicker'

test('loads and displays CPicker component', async () => {
  const { container } = render(<CPicker>Test</CPicker>)
  expect(container).toMatchSnapshot()
})
