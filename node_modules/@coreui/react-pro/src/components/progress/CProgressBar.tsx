import React, { forwardRef, HTMLAttributes, useContext } from 'react'
import PropTypes from 'prop-types'
import classNames from 'classnames'

import { CProgressStackedContext } from './CProgressStacked'
import { colorPropType, gradientsPropType } from '../../props'
import type { Colors, Gradients } from '../../types'

export interface CProgressBarProps extends HTMLAttributes<HTMLDivElement> {
  /**
   * Use to animate the stripes right to left via CSS3 animations.
   */
  animated?: boolean
  /**
   * A string of all className you want applied to the component.
   */
  className?: string
  /**
   * Sets the color context of the component to one of CoreUI’s themed colors.
   *
   * @type {'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | 'primary-gradient' | 'secondary-gradient' | 'success-gradient' | 'danger-gradient' | 'warning-gradient' | 'info-gradient' | 'dark-gradient' | 'light-gradient' | string }
   */
  color?: Colors | Gradients
  /**
   * The percent to progress the ProgressBar.
   */
  value?: number
  /**
   * Set the progress bar variant to optional striped.
   */
  variant?: 'striped'
}

export const CProgressBar = forwardRef<HTMLDivElement, CProgressBarProps>(
  ({ children, animated, className, color, value = 0, variant, ...rest }, ref) => {
    const { stacked } = useContext(CProgressStackedContext)

    return (
      <div
        className={classNames(
          'progress-bar',
          {
            [`bg-${color}`]: color,
            [`progress-bar-${variant}`]: variant,
            'progress-bar-animated': animated,
          },
          className,
        )}
        {...(!stacked && { style: { width: `${value}%` } })}
        {...rest}
        ref={ref}
      >
        {children}
      </div>
    )
  },
)
CProgressBar.propTypes = {
  animated: PropTypes.bool,
  children: PropTypes.node,
  className: PropTypes.string,
  color: PropTypes.oneOfType([colorPropType, gradientsPropType]),
  value: PropTypes.number,
  variant: PropTypes.oneOf(['striped']),
}

CProgressBar.displayName = 'CProgressBar'
