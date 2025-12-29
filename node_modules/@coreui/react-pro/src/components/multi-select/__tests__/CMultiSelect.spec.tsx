import * as React from 'react'
import { render, fireEvent } from '@testing-library/react'
import '@testing-library/jest-dom/extend-expect'
import { CMultiSelect } from '../../../index'

const options = [
  {
    value: 0,
    text: 'Angular',
  },
  {
    value: 1,
    text: 'Bootstrap',
    selected: true,
  },
  {
    value: 2,
    text: 'React.js',
  },
  {
    value: 3,
    text: 'Vue.js',
    selected: true,
  },
  {
    label: 'backend',
    options: [
      {
        value: 4,
        text: 'Django',
      },
      {
        value: 5,
        text: 'Laravel',
      },
      {
        value: 6,
        text: 'Node.js',
        disabled: true,
        selected: true,
      },
    ],
  },
]

test('loads and displays CMultiSelect component', async () => {
  const { container } = render(<CMultiSelect options={[]} />)
  expect(container).toMatchSnapshot()
})

test('CMultiSelect customize', async () => {
  const { container } = render(
    <CMultiSelect
      options={options}
      className="bazinga"
      cleaner={true}
      multiple={true}
      optionsMaxHeight={150}
      optionsStyle="checkbox"
      placeholder="placeholder"
      search={true}
      searchNoResultsLabel="searchNoResultsLabel"
      selectAll={true}
      selectAllLabel="selectAllLabel"
      selectionType="tags"
      selectionTypeCounterText="selectionTypeCounterText"
      visible={true}
    />,
  )
  expect(container).toMatchSnapshot()
  expect(container.firstChild).toHaveAttribute('multiple', '')
  expect(container.firstChild).toHaveAttribute('style', 'display: none;')
  expect(container.firstChild).toHaveAttribute('tabindex', '-1')
  if (container.firstChild === null) {
    expect(true).toBe(false)
  } else {
    expect(container.firstChild.firstChild).toHaveAttribute('value', '1')
    expect(container.firstChild.firstChild).toHaveTextContent('Bootstrap')
    expect(container.firstChild.lastChild).toHaveAttribute('value', '6')
    expect(container.firstChild.lastChild).toHaveTextContent('Node.js')
  }
  expect(container.lastChild).toHaveClass('form-multi-select')
  expect(container.lastChild).toHaveClass('show')
  expect(container.lastChild).toHaveClass('bazinga')

  if (container.lastChild === null) {
    expect(true).toBe(false)
  } else {
    expect(container.lastChild.firstChild).toHaveClass('form-multi-select-toggler')
    if (container.lastChild.firstChild === null) {
      expect(true).toBe(false)
    } else {
      expect(container.lastChild.firstChild.firstChild).toHaveClass(
        'form-multi-select-selection-tags',
      )
      if (container.lastChild.firstChild.firstChild === null) {
        expect(true).toBe(false)
      } else {
        expect(container.lastChild.firstChild.firstChild.firstChild).toHaveClass(
          'form-multi-select-tag',
        )
        expect(container.lastChild.firstChild.firstChild.firstChild).toHaveTextContent('Bootstrap')
      }
    }
    expect(container.lastChild.lastChild).toHaveClass('form-multi-select-dropdown')
    if (container.lastChild.lastChild === null) {
      expect(true).toBe(false)
    } else {
      expect(container.lastChild.lastChild.firstChild).toHaveClass('form-multi-select-all')
      expect(container.lastChild.lastChild.firstChild).toHaveAttribute('type', 'button')
      expect(container.lastChild.lastChild.firstChild).toHaveTextContent('selectAllLabel')
      expect(container.lastChild.lastChild.lastChild).toHaveClass('form-multi-select-options')
      expect(container.lastChild.lastChild.lastChild).toHaveAttribute(
        'style',
        'max-height: 150px; overflow: scroll;',
      )
      if (container.lastChild.lastChild.lastChild === null) {
        expect(true).toBe(false)
      } else {
        expect(container.lastChild.lastChild.lastChild.firstChild).toHaveClass(
          'form-multi-select-option',
        )
        expect(container.lastChild.lastChild.lastChild.firstChild).toHaveClass(
          'form-multi-select-option-with-checkbox',
        )
        expect(container.lastChild.lastChild.lastChild.firstChild).toHaveTextContent('Angular')
        expect(container.lastChild.lastChild.lastChild.lastChild).toHaveClass(
          'form-multi-select-option',
        )
        expect(container.lastChild.lastChild.lastChild.lastChild).toHaveClass(
          'form-multi-select-option-with-checkbox',
        )
        expect(container.lastChild.lastChild.lastChild.lastChild).toHaveClass('form-multi-selected')
        expect(container.lastChild.lastChild.lastChild.lastChild).toHaveClass('disabled')
        expect(container.lastChild.lastChild.lastChild.lastChild).toHaveTextContent('Node.js')
      }
    }
  }
})

test('CMultiSelect fire events', async () => {
  const event = jest.fn()
  expect(event).toHaveBeenCalledTimes(0)
  render(
    <CMultiSelect
      options={options}
      className="bazinga"
      cleaner={true}
      multiple={true}
      optionsMaxHeight={150}
      optionsStyle="checkbox"
      placeholder="placeholder"
      search={true}
      searchNoResultsLabel="searchNoResultsLabel"
      selectAll={true}
      selectAllLabel="selectAllLabel"
      selectionType="tags"
      selectionTypeCounterText="selectionTypeCounterText"
      visible={true}
      onChange={event}
    />,
  )
  expect(event).toHaveBeenCalledTimes(1)
  const option = document.querySelector('.form-multi-select-option')
  if (option !== null) {
    fireEvent.click(option)
  }
  expect(event).toHaveBeenCalledTimes(2)
  const removeButton = document.querySelector('.form-multi-select-tag-delete')
  if (removeButton !== null) {
    fireEvent.click(removeButton)
  }
  expect(event).toHaveBeenCalledTimes(3)
})
