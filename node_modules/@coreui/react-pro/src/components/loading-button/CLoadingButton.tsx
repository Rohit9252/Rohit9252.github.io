import React, { useEffect, useState, forwardRef } from 'react'
import PropTypes from 'prop-types'
import classNames from 'classnames'
import { CButton, CButtonProps } from './../button/CButton'
import { CSpinner } from './../spinner/CSpinner'
export interface CLoadingButtonProps extends CButtonProps {
  /**
   * A string of all className you want applied to the base component.
   */
  className?: string
  /**
   * Makes button disabled when loading.
   */
  disabledOnLoading?: boolean
  /**
   * Loading state (set to true to start animation).
   */
  loading?: boolean
  /**
   * @ignore
   */
  onClick?: () => void
  /**
   * Sets type of spinner.
   */
  spinnerType?: 'border' | 'grow'
  /**
   * Automatically starts loading animation and stops after a determined amount of milliseconds.
   */
  timeout?: number
}

export const CLoadingButton = forwardRef<HTMLButtonElement, CLoadingButtonProps>(
  (
    {
      children,
      className,
      disabledOnLoading,
      loading,
      onClick,
      spinnerType = 'border',
      timeout,
      ...rest
    },
    ref,
  ) => {
    const [_loading, setLoading] = useState<boolean>()

    useEffect(() => {
      setLoading(loading)
    }, [loading])

    const handleOnClick = () => {
      onClick && onClick()
      if (timeout) {
        setLoading(true)
        setTimeout(() => {
          setLoading(false)
        }, timeout)
      }
    }

    return (
      <CButton
        className={classNames('btn-loading', _loading && 'is-loading', className)}
        {...(disabledOnLoading && _loading && { disabled: true })}
        onClick={handleOnClick}
        {...rest}
        ref={ref}
      >
        <CSpinner className="btn-loading-spinner" size="sm" variant={spinnerType} />
        {children}
      </CButton>
    )
  },
)

CLoadingButton.propTypes = {
  children: PropTypes.node,
  className: PropTypes.string,
  disabledOnLoading: PropTypes.bool,
  loading: PropTypes.bool,
  onClick: PropTypes.func,
  spinnerType: PropTypes.oneOf(['border', 'grow']),
  timeout: PropTypes.number,
}

CLoadingButton.displayName = 'CLoadingButton'
