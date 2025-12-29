import * as React from 'react'
import { render } from '@testing-library/react'
import '@testing-library/jest-dom/extend-expect'
import { CMultiSelectNativeSelect } from '../CMultiSelectNativeSelect'
import { Option } from '../types'

test('loads and displays CMultiSelectNativeSelect component', async () => {
  const { container } = render(<CMultiSelectNativeSelect options={[]} />)
  expect(container).toMatchSnapshot()
})

test('CMultiSelectNativeSelect customize', async () => {
  const options: Option[] = [
    {
      text: 'text1',
      value: 'value1',
    },
    {
      text: 'text2',
      value: 'value2',
      disabled: true,
      label: 'label2',
      order: 4,
      selected: true,
    },
    {
      text: 'text3',
      value: 'value3',
      order: 3,
    },
  ]
  const { container } = render(
    <CMultiSelectNativeSelect multiple={true} options={options} value="3" />,
  )
  expect(container).toMatchSnapshot()
})
