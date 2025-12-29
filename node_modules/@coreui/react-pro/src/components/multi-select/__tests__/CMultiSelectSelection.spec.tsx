import * as React from 'react'
import { render, fireEvent } from '@testing-library/react'
import '@testing-library/jest-dom/extend-expect'
import { CMultiSelectSelection } from '../CMultiSelectSelection'

const selected = [
  {
    text: 'text1',
    value: 'value1',
  },
  {
    text: 'text2',
    value: 'value2',
    disabled: true,
  },
]

test('loads and displays CMultiSelectSelection component', async () => {
  const { container } = render(<CMultiSelectSelection />)
  expect(container).toMatchSnapshot()
})

test('CMultiSelectSelection customize tags', async () => {
  const { container } = render(
    <CMultiSelectSelection
      multiple={true}
      search={true}
      selected={selected}
      selectionType="tags"
      selectionTypeCounterText="text"
    />,
  )
  expect(container).toMatchSnapshot()
  expect(container.firstChild).toHaveClass('form-multi-select-selection')
  if (container.firstChild === null) {
    expect(true).toBe(false)
  } else {
    expect(container.firstChild.firstChild).toHaveClass('form-multi-select-tag')
    expect(container.firstChild.lastChild).toHaveClass('form-multi-select-tag')
    if (container.firstChild.firstChild === null) {
      expect(true).toBe(false)
    } else {
      expect(container.firstChild.firstChild.lastChild).toHaveClass('form-multi-select-tag-delete')
      expect(container.firstChild.firstChild.lastChild).toHaveAttribute('aria-label', 'Close')
      if (container.firstChild.firstChild.lastChild === null) {
        expect(true).toBe(false)
      } else {
        expect(container.firstChild.firstChild.lastChild.firstChild).toHaveAttribute(
          'aria-hidden',
          'true',
        )
        expect(container.firstChild.firstChild.lastChild.firstChild).toHaveTextContent('×')
      }
    }
  }
})

test('CMultiSelectSelection customize counter', async () => {
  const { container } = render(
    <CMultiSelectSelection
      multiple={true}
      search={false}
      selected={selected}
      selectionType="counter"
      selectionTypeCounterText="text"
    />,
  )
  expect(container).toMatchSnapshot()
  expect(container.firstChild).toHaveClass('form-multi-select-selection')
  expect(container.firstChild).toHaveTextContent('2 text')
})

test('CMultiSelectSelection customize text', async () => {
  const { container } = render(
    <CMultiSelectSelection
      multiple={true}
      search={true}
      selected={selected}
      selectionType="text"
      selectionTypeCounterText="text"
    />,
  )
  expect(container).toMatchSnapshot()
  expect(container.firstChild).toHaveClass('form-multi-select-selection')
  expect(container.firstChild).toHaveTextContent('text1, text2')
})

test('CMultiSelectSelection test remove event', async () => {
  const onRemove = jest.fn()
  render(
    <CMultiSelectSelection
      multiple={true}
      selected={selected}
      selectionType="tags"
      onRemove={onRemove}
    />,
  )
  expect(onRemove).toHaveBeenCalledTimes(0)
  const removeButton = document.querySelector('.form-multi-select-tag-delete')
  if (removeButton !== null) {
    fireEvent.click(removeButton)
  }
  expect(onRemove).toHaveBeenCalledTimes(1)
})
