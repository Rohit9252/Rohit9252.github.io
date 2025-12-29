import React, { forwardRef, HTMLAttributes } from 'react'
import PropTypes from 'prop-types'
import classNames from 'classnames'

import { colorPropType, gradientsPropType } from '../../props'
import type { Colors, Gradients } from '../../types'

export interface CCardProps extends HTMLAttributes<HTMLDivElement> {
  /**
   * A string of all className you want applied to the base component.
   */
  className?: string
  /**
   * Sets the color context of the component to one of CoreUI’s themed colors.
   *
   * @type {'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | 'primary-gradient' | 'secondary-gradient' | 'success-gradient' | 'danger-gradient' | 'warning-gradient' | 'info-gradient' | 'dark-gradient' | 'light-gradient' | string }
   */
  color?: Colors | Gradients
  /**
   * Sets the text color context of the component to one of CoreUI’s themed colors.
   *
   * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | 'white' | 'muted' | 'high-emphasis' | 'medium-emphasis' | 'disabled' | 'high-emphasis-inverse' | 'medium-emphasis-inverse' | 'disabled-inverse' | string
   */
  textColor?: string
}

export const CCard = forwardRef<HTMLDivElement, CCardProps>(
  ({ children, className, color, textColor, ...rest }, ref) => {
    return (
      <div
        className={classNames(
          'card',
          {
            [`bg-${color}`]: color,
            [`text-${textColor}`]: textColor,
          },
          className,
        )}
        {...rest}
        ref={ref}
      >
        {children}
      </div>
    )
  },
)

CCard.propTypes = {
  children: PropTypes.node,
  className: PropTypes.string,
  color: PropTypes.oneOfType([colorPropType, gradientsPropType]),
  textColor: PropTypes.string,
}

CCard.displayName = 'CCard'
