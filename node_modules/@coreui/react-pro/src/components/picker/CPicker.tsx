import React, { forwardRef, HTMLAttributes, ReactNode, useEffect, useRef, useState } from 'react'

import PropTypes from 'prop-types'
import classNames from 'classnames'
import { Placement } from '@popperjs/core'

import { useForkedRef, usePopper } from '../../hooks'
import { isRTL } from '../../utils'

export interface CPickerProps extends HTMLAttributes<HTMLDivElement> {
  /**
   * Set container type for the component.
   */
  container?: 'dropdown' | 'inline'
  /**
   * Toggle the disabled state for the component.
   */
  disabled?: boolean
  /**
   * A string of all className you want applied to the dropdown menu.
   */
  dropdownClassNames?: string
  /**
   * Toggle visibility of footer element or set the content of footer.
   */
  footer?: boolean | ReactNode
  /**
   * Add custom elements to the footer.
   */
  footerContent?: ReactNode
  /**
   * Callback fired when the component requests to be hidden.
   */
  onHide?: () => void
  /**
   * Callback fired when the component requests to be shown.
   */
  onShow?: () => void
  /**
   * The content of toggler.
   */
  toggler?: ReactNode
  /**
   * Toggle the visibility of dropdown menu component.
   */
  visible?: boolean
}

export const CPicker = forwardRef<HTMLDivElement | HTMLLIElement, CPickerProps>(
  (
    {
      children,
      className,
      container = 'dropdown',
      disabled,
      dropdownClassNames,
      footer,
      footerContent,
      onHide,
      onShow,
      toggler,
      visible,
    },
    ref,
  ) => {
    const pickerRef = useRef<HTMLDivElement>(null)
    const pickerForkedRef = useForkedRef(ref, pickerRef)
    const dropdownRef = useRef<HTMLDivElement>(null)
    const togglerRef = useRef<HTMLDivElement>(null)

    const { initPopper, destroyPopper } = usePopper()

    const [_visible, setVisible] = useState(visible)

    const popperConfig = {
      placement: (isRTL(pickerRef.current) ? 'bottom-end' : 'bottom-start') as Placement,
      modifiers: [
        {
          name: 'preventOverflow',
          options: {
            boundary: 'clippingParents',
          },
        },
        {
          name: 'offset',
          options: {
            offset: [0, 2],
          },
        },
      ],
    }

    useEffect(() => {
      setVisible(visible)
    }, [visible])

    useEffect(() => {
      if (container !== 'inline' && _visible) {
        onShow && onShow()

        window.addEventListener('mouseup', handleMouseUp)
        window.addEventListener('keyup', handleKeyUp)

        togglerRef.current &&
          dropdownRef.current &&
          initPopper(togglerRef.current, dropdownRef.current, popperConfig)
      }

      return () => {
        onHide && onHide()

        window.removeEventListener('mouseup', handleMouseUp)
        window.removeEventListener('keyup', handleKeyUp)

        destroyPopper()
      }
    }, [_visible])

    const handleKeyUp = (event: KeyboardEvent) => {
      if (event.key === 'Escape') {
        setVisible(false)
      }
    }

    const handleMouseUp = (event: Event) => {
      if (pickerRef.current && pickerRef.current.contains(event.target as HTMLElement)) {
        return
      }

      setVisible(false)
    }

    switch (container) {
      case 'inline': {
        return (
          <div className={classNames('picker', className)} ref={pickerForkedRef}>
            {children}
          </div>
        )
      }
      default: {
        return (
          <div
            className={classNames('dropdown', 'picker', className, {
              show: _visible,
            })}
            onClick={() => !disabled && setVisible(true)}
            ref={pickerForkedRef}
          >
            {toggler &&
              React.isValidElement(toggler) &&
              React.cloneElement(toggler as React.ReactElement<any>, {
                ref: togglerRef,
              })}
            <div
              className={classNames(
                'dropdown-menu',
                {
                  show: _visible,
                },
                dropdownClassNames,
              )}
              ref={dropdownRef}
            >
              {children}
              {footer && footerContent}
            </div>
          </div>
        )
      }
    }
  },
)

CPicker.displayName = 'CPicker'

CPicker.propTypes = {
  children: PropTypes.node,
  className: PropTypes.string,
  container: PropTypes.oneOf(['dropdown', 'inline']),
  disabled: PropTypes.bool,
  dropdownClassNames: PropTypes.string,
  footer: PropTypes.oneOfType([PropTypes.bool, PropTypes.node]),
  footerContent: PropTypes.node,
  onHide: PropTypes.func,
  onShow: PropTypes.func,
  toggler: PropTypes.node,
}
