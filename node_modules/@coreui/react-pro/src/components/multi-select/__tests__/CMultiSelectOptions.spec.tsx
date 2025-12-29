import * as React from 'react'
import { render, fireEvent } from '@testing-library/react'
import '@testing-library/jest-dom/extend-expect'
import { CMultiSelectOptions } from '../CMultiSelectOptions'
import { Option } from '../types'

const options: Option[] = [
  {
    text: 'text1',
    value: 'value1',
    selected: true,
    disabled: true,
  },
  {
    text: 'text3',
    value: 'value3',
  },
]

test('loads and displays CMultiSelectOptions component', async () => {
  const { container } = render(
    <CMultiSelectOptions options={[]} searchNoResultsLabel="some no result label" selected={[]} />,
  )
  expect(container).toMatchSnapshot()
  expect(container.firstChild).toHaveClass('form-multi-select-options')
  if (container.firstChild === null) {
    expect(true).toBe(false)
  } else {
    expect(container.firstChild.firstChild).toHaveClass('form-multi-select-options-empty')
    expect(container.firstChild.firstChild).toHaveTextContent('some no result label')
  }
})

test('CMultiSelectOptions customize', async () => {
  const { container } = render(
    <CMultiSelectOptions
      options={options}
      optionsMaxHeight="200"
      optionsStyle="checkbox"
      searchNoResultsLabel="some - searchNoResultsLabel"
      selected={[]}
    />,
  )
  expect(container).toMatchSnapshot()
  expect(container.firstChild).toHaveClass('form-multi-select-options')
  expect(container.firstChild).toHaveAttribute('style', 'max-height: 200; overflow: scroll;')
  if (container.firstChild === null) {
    expect(true).toBe(false)
  } else {
    expect(container.firstChild.firstChild).toHaveClass('form-multi-select-option')
    expect(container.firstChild.firstChild).toHaveClass('form-multi-select-option-with-checkbox')
    expect(container.firstChild.firstChild).toHaveClass('disabled')
    expect(container.firstChild.firstChild).toHaveTextContent('text1')
    expect(container.firstChild.lastChild).toHaveClass('form-multi-select-option')
    expect(container.firstChild.lastChild).toHaveClass('form-multi-select-option-with-checkbox')
    expect(container.firstChild.lastChild).toHaveTextContent('text3')
  }
})

test('CMultiSelectOptions handle on click', async () => {
  const onClick = jest.fn()
  render(<CMultiSelectOptions options={options} handleOptionOnClick={onClick} selected={[]} />)
  expect(onClick).toHaveBeenCalledTimes(0)
  const option = document.querySelector('.form-multi-select-option')
  if (option !== null) {
    fireEvent.click(option)
  }
  expect(onClick).toHaveBeenCalledTimes(1)
})
