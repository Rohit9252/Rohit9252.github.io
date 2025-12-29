import * as React from 'react'
import { render, fireEvent } from '@testing-library/react'
import '@testing-library/jest-dom/extend-expect'
import { CLoadingButton } from '../../../index'

test('loads and displays CLoadingButton component', async () => {
  const { container } = render(<CLoadingButton />)
  expect(container).toMatchSnapshot()
})

test('CLoadingButton customize', async () => {
  const { container } = render(
    <CLoadingButton
      className="bazinga"
      disabledOnLoading={true}
      loading={true}
      spinnerType="grow"
      timeout={1000}
    >
      Text
    </CLoadingButton>,
  )
  expect(container).toMatchSnapshot()
  expect(container.firstChild).toHaveClass('btn-loading')
  expect(container.firstChild).toHaveClass('is-loading')
  expect(container.firstChild).toHaveClass('bazinga')
  expect(container.firstChild).toHaveAttribute('disabled', '')
  expect(container.firstChild).toHaveTextContent('Text')
  if (container.firstChild === null) {
    expect(true).toBe(false)
  } else {
    expect(container.firstChild.firstChild).toHaveClass('btn-loading-spinner')
    expect(container.firstChild.firstChild).toHaveClass('spinner-grow')
    expect(container.firstChild.firstChild).toHaveClass('spinner-grow-sm')
  }
})

test('CLoadingButton test event on click', async () => {
  const onClick = jest.fn()
  render(<CLoadingButton onClick={onClick}>Text</CLoadingButton>)
  expect(onClick).toHaveBeenCalledTimes(0)
  const button = document.querySelector('.btn-loading')
  if (button !== null) {
    fireEvent.click(button)
  }
  expect(onClick).toHaveBeenCalledTimes(1)
})
