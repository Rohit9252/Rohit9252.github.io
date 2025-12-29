import React, { forwardRef, ReactNode, useEffect, useRef, useState } from 'react'
import PropTypes from 'prop-types'
import classNames from 'classnames'

import { CButton } from '../button'
import { CFormControlWrapper, CFormControlWrapperProps } from '../form/CFormControlWrapper'
import { CPicker, CPickerProps } from './../picker/CPicker'

import { CTimePickerRollCol } from './CTimePickerRollCol'
import {
  convert12hTo24h,
  convertTimeToDate,
  getAmPm,
  getLocalizedTimePartials,
  getSelectedHour,
  getSelectedMinutes,
  getSelectedSeconds,
  isValidTime,
} from './utils'

import { Colors } from '../../types'
import type { LocalizedTimePartials } from './types'

export interface CTimePickerProps
  extends Omit<CFormControlWrapperProps, 'floatingLabel'>,
    Omit<CPickerProps, 'placeholder'> {
  /**
   * Set if the component should use the 12/24 hour format. If `true` forces the interface to a 12-hour format. If `false` forces the interface into a 24-hour format. If `auto` the current locale will determine the 12 or 24-hour interface by default locales.
   *
   * @since 4.8.0
   */
  ampm?: 'auto' | boolean
  /**
   * A string of all className you want applied to the component.
   */
  className?: string
  /**
   * Toggle visibility or set the content of cancel button.
   */
  cancelButton?: boolean | ReactNode
  /**
   * Sets the color context of the cancel button to one of CoreUI’s themed colors.
   *
   * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | string
   */
  cancelButtonColor?: Colors
  /**
   * Size the cancel button small or large.
   */
  cancelButtonSize?: 'sm' | 'lg'
  /**
   * Set the cancel button variant to an outlined button or a ghost button.
   */
  cancelButtonVariant?: 'outline' | 'ghost'
  /**
   * A string of all className you want applied to the component.
   */
  /**
   * Toggle visibility or set the content of the cleaner button.
   */
  cleaner?: ReactNode | boolean
  /**
   * Toggle visibility or set the content of confirm button.
   */
  confirmButton?: boolean | ReactNode
  /**
   * Sets the color context of the confirm button to one of CoreUI’s themed colors.
   *
   * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | string
   */
  confirmButtonColor?: Colors
  /**
   * Size the confirm button small or large.
   */
  confirmButtonSize?: 'sm' | 'lg'
  /**
   * Set the confirm button variant to an outlined button or a ghost button.
   */
  confirmButtonVariant?: 'outline' | 'ghost'
  /**
   * Toggle visibility or set the content of the input indicator.
   */
  indicator?: ReactNode | boolean
  /**
   * Toggle the readonly state for the component.
   */
  inputReadOnly?: boolean
  /**
   * Sets the default locale for components. If not set, it is inherited from the browser.
   */
  locale?: string
  /**
   * Callback fired when the time changed.
   */
  onTimeChange?: (timeString: string | null, localeTimeString?: string, date?: Date) => void
  /**
   * Specifies a short hint that is visible in the input.
   */
  placeholder?: string
  /**
   * When present, it specifies that time must be filled out before submitting the form.
   *
   * @since 4.10.0
   */
  required?: boolean
  /**
   * Show seconds.
   *
   * @since 4.8.0
   */
  seconds?: boolean
  /**
   * Size the component small or large.
   */
  size?: 'sm' | 'lg'
  /**
   * Initial selected time.
   */
  time?: Date | string | null
  /**
   * Set the time picker variant to a roll or select.
   */
  variant?: 'roll' | 'select'
}

export const CTimePicker = forwardRef<HTMLDivElement | HTMLLIElement, CTimePickerProps>(
  (
    {
      ampm = 'auto',
      cancelButton = 'Cancel',
      cancelButtonColor = 'primary',
      cancelButtonSize = 'sm',
      cancelButtonVariant = 'ghost',
      className,
      cleaner = true,
      confirmButton = 'OK',
      confirmButtonColor = 'primary',
      confirmButtonSize = 'sm',
      confirmButtonVariant,
      container = 'dropdown',
      disabled,
      feedback,
      feedbackInvalid,
      feedbackValid,
      footer = true,
      id,
      indicator = true,
      inputReadOnly,
      invalid,
      label,
      locale = 'default',
      onTimeChange,
      onHide,
      onShow,
      placeholder = 'Select time',
      required,
      seconds = true,
      size,
      text,
      time,
      tooltipFeedback,
      valid,
      variant = 'roll',
      visible,
      ...rest
    },
    ref,
  ) => {
    const formRef = useRef<HTMLFormElement>()
    const inputRef = useRef<HTMLInputElement>(null)

    const [date, setDate] = useState<Date | null>(convertTimeToDate(time))
    const [initialDate, setInitialDate] = useState<Date | null>(null)
    const [isValid, setIsValid] = useState(valid ?? (invalid === true ? false : undefined))
    const [_ampm, setAmPm] = useState<'am' | 'pm'>(date ? getAmPm(new Date(date), locale) : 'am')
    const [_visible, setVisible] = useState(visible)

    const [localizedTimePartials, setLocalizedTimePartials] = useState<LocalizedTimePartials>({
      listOfHours: [],
      listOfMinutes: [],
      listOfSeconds: [],
      hour12: false,
    })

    useEffect(() => {
      setDate(time ? convertTimeToDate(time) : null)
    }, [time])

    useEffect(() => {
      setIsValid(valid ?? (invalid === true ? false : undefined))
    }, [valid, invalid])

    useEffect(() => {
      setLocalizedTimePartials(getLocalizedTimePartials(locale, ampm))

      if (inputRef.current) {
        inputRef.current.value = date
          ? date.toLocaleTimeString(locale, {
              hour12: localizedTimePartials && localizedTimePartials.hour12,
              ...(!seconds && { timeStyle: 'short' }),
            })
          : ''
      }

      date && setAmPm(getAmPm(new Date(date), locale))
    }, [date])

    useEffect(() => {
      if (inputRef.current && inputRef.current.form) {
        formRef.current = inputRef.current.form
      }
    }, [inputRef])

    useEffect(() => {
      if (formRef.current) {
        formRef.current.addEventListener('submit', (event) => {
          setTimeout(() => handleFormValidation(event.target as HTMLFormElement))
        })

        handleFormValidation(formRef.current)
      }
    }, [formRef, date])

    const handleClear = (event: React.MouseEvent<HTMLElement>) => {
      event.stopPropagation()
      setDate(null)
      onTimeChange && onTimeChange(null)
    }

    const handleFormValidation = (form: HTMLFormElement) => {
      if (!form.classList.contains('was-validated')) {
        return
      }

      if (date) {
        return setIsValid(true)
      }

      setIsValid(false)
    }

    const handleTimeChange = (set: 'hours' | 'minutes' | 'seconds' | 'toggle', value: string) => {
      const _date = date || new Date('1970-01-01')

      if (set === 'toggle') {
        if (value === 'am') {
          _date.setHours(_date.getHours() - 12)
        }
        if (value === 'pm') {
          _date.setHours(_date.getHours() + 12)
        }
      }

      if (set === 'hours') {
        if (localizedTimePartials && localizedTimePartials.hour12) {
          _date.setHours(convert12hTo24h(_ampm, Number.parseInt(value)))
        } else {
          _date.setHours(Number.parseInt(value))
        }
      }

      if (set === 'minutes') {
        _date.setMinutes(Number.parseInt(value))
      }

      if (set === 'seconds') {
        _date.setSeconds(Number.parseInt(value))
      }

      setDate(new Date(_date))
      onTimeChange && onTimeChange(_date.toTimeString(), _date.toLocaleTimeString(), _date)
    }

    const InputGroup = () => (
      <div
        className={classNames('input-group', 'picker-input-group', {
          [`input-group-${size}`]: size,
        })}
      >
        <input
          autoComplete="off"
          className="form-control"
          disabled={disabled}
          onChange={(event) =>
            isValidTime(event.target.value) && setDate(convertTimeToDate(event.target.value))
          }
          placeholder={placeholder}
          readOnly={inputReadOnly}
          required={required}
          ref={inputRef}
        />
        {(indicator || cleaner) && (
          <span className="input-group-text">
            {indicator && (
              <span className="picker-input-group-indicator">
                {typeof indicator === 'boolean' ? (
                  <span className="picker-input-group-icon time-picker-input-icon" />
                ) : (
                  indicator
                )}
              </span>
            )}
            {cleaner && date && (
              <span
                className="picker-input-group-cleaner"
                role="button"
                onClick={(event) => handleClear(event)}
              >
                {typeof cleaner === 'boolean' ? (
                  <span className="picker-input-group-icon time-picker-cleaner-icon" />
                ) : (
                  cleaner
                )}
              </span>
            )}
          </span>
        )}
      </div>
    )

    const TimePickerSelect = () => {
      return (
        <>
          <span className="time-picker-inline-icon" />
          <select
            className="form-select"
            disabled={disabled}
            onChange={(event: React.ChangeEvent<HTMLSelectElement>) =>
              handleTimeChange('hours', event.target.value)
            }
            value={getSelectedHour(date, locale)}
          >
            {localizedTimePartials &&
              localizedTimePartials.listOfHours.map((option, index) => (
                <option value={option.value.toString()} key={index}>
                  {option.label}
                </option>
              ))}
          </select>
          <>:</>
          <select
            className="form-select"
            disabled={disabled}
            onChange={(event: React.ChangeEvent<HTMLSelectElement>) =>
              handleTimeChange('minutes', event.target.value)
            }
            value={getSelectedMinutes(date)}
          >
            {localizedTimePartials &&
              localizedTimePartials.listOfMinutes.map((option, index) => (
                <option value={option.value.toString()} key={index}>
                  {option.label}
                </option>
              ))}
          </select>
          {seconds && (
            <>
              <>:</>
              <select
                className="form-select"
                disabled={disabled}
                onChange={(event: React.ChangeEvent<HTMLSelectElement>) =>
                  handleTimeChange('seconds', event.target.value)
                }
                value={getSelectedSeconds(date)}
              >
                {localizedTimePartials &&
                  localizedTimePartials.listOfSeconds.map((option, index) => (
                    <option value={option.value.toString()} key={index}>
                      {option.label}
                    </option>
                  ))}
              </select>
            </>
          )}
          {localizedTimePartials && localizedTimePartials.hour12 && (
            <select
              className="form-select"
              disabled={disabled}
              onChange={(event: React.ChangeEvent<HTMLSelectElement>) =>
                handleTimeChange('toggle', event.target.value)
              }
              value={_ampm}
            >
              <option value="am">AM</option>
              <option value="pm">PM</option>
            </select>
          )}
        </>
      )
    }

    return (
      <CFormControlWrapper
        describedby={rest['aria-describedby']}
        feedback={feedback}
        feedbackInvalid={feedbackInvalid}
        feedbackValid={feedbackValid}
        id={id}
        invalid={isValid === false ? true : false}
        label={label}
        text={text}
        tooltipFeedback={tooltipFeedback}
        valid={isValid}
      >
        <CPicker
          className={classNames(
            'time-picker',
            {
              [`time-picker-${size}`]: size,
              disabled: disabled,
              'is-invalid': isValid === false ? true : false,
              'is-valid': isValid,
            },
            className,
          )}
          container={container}
          disabled={disabled}
          dropdownClassNames="time-picker-dropdown"
          footer={footer}
          footerContent={
            <div className="picker-footer">
              {cancelButton && (
                <CButton
                  color={cancelButtonColor}
                  size={cancelButtonSize}
                  variant={cancelButtonVariant}
                  onClick={() => {
                    initialDate && setDate(new Date(initialDate))
                    setVisible(false)
                  }}
                >
                  {cancelButton}
                </CButton>
              )}
              {confirmButton && (
                <CButton
                  color={confirmButtonColor}
                  size={confirmButtonSize}
                  variant={confirmButtonVariant}
                  onClick={() => {
                    setVisible(false)
                  }}
                >
                  {confirmButton}
                </CButton>
              )}
            </div>
          }
          id={id}
          onHide={() => {
            setVisible(false)
            onHide && onHide()
          }}
          onShow={() => {
            date && setInitialDate(new Date(date))
            setVisible(true)
            onShow && onShow()
          }}
          toggler={InputGroup()}
          visible={_visible}
          {...rest}
          ref={ref}
        >
          <div
            className={classNames('time-picker-body', {
              ['time-picker-roll']: variant === 'roll',
            })}
          >
            {variant === 'select' ? (
              <TimePickerSelect />
            ) : (
              <>
                <CTimePickerRollCol
                  elements={localizedTimePartials && localizedTimePartials.listOfHours}
                  onClick={(index: number) => handleTimeChange('hours', index.toString())}
                  selected={getSelectedHour(date, locale, ampm)}
                />
                <CTimePickerRollCol
                  elements={localizedTimePartials && localizedTimePartials.listOfMinutes}
                  onClick={(index: number) => handleTimeChange('minutes', index.toString())}
                  selected={getSelectedMinutes(date)}
                />
                {seconds && (
                  <CTimePickerRollCol
                    elements={localizedTimePartials && localizedTimePartials.listOfSeconds}
                    onClick={(index: number) => handleTimeChange('seconds', index.toString())}
                    selected={getSelectedSeconds(date)}
                  />
                )}
                {localizedTimePartials && localizedTimePartials.hour12 && (
                  <CTimePickerRollCol
                    elements={[
                      { value: 'am', label: 'AM' },
                      { value: 'pm', label: 'PM' },
                    ]}
                    onClick={(value: string) => handleTimeChange('toggle', value)}
                    selected={_ampm}
                  />
                )}
              </>
            )}
          </div>
        </CPicker>
      </CFormControlWrapper>
    )
  },
)

CTimePicker.propTypes = {
  ...CFormControlWrapper.propTypes,
  ...CPicker.propTypes,
  ampm: PropTypes.oneOfType([PropTypes.oneOf<'auto'>(['auto']), PropTypes.bool]),
  cancelButton: PropTypes.oneOfType([PropTypes.bool, PropTypes.node]),
  cancelButtonColor: CButton.propTypes?.color,
  cancelButtonSize: CButton.propTypes?.size,
  cancelButtonVariant: CButton.propTypes?.variant,
  className: PropTypes.string,
  confirmButton: PropTypes.oneOfType([PropTypes.bool, PropTypes.node]),
  confirmButtonColor: CButton.propTypes?.color,
  confirmButtonSize: CButton.propTypes?.size,
  confirmButtonVariant: CButton.propTypes?.variant,
  locale: PropTypes.string,
  onTimeChange: PropTypes.func,
  required: PropTypes.bool,
  seconds: PropTypes.bool,
  time: PropTypes.oneOfType([PropTypes.instanceOf(Date), PropTypes.string]),
  variant: PropTypes.oneOf(['roll', 'select']),
}

CTimePicker.displayName = 'CTimePicker'
