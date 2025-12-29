import React, { forwardRef, ReactNode, useEffect, useRef, useState } from 'react'

import classNames from 'classnames'
import { format as dateFormat } from 'date-fns'
import PropTypes from 'prop-types'
import { isMobile } from 'react-device-detect'

import { CButton } from '../button'
import { CCalendar, CCalendarProps } from '../calendar/CCalendar'
import { CFormControlWrapper, CFormControlWrapperProps } from '../form/CFormControlWrapper'
import { CPicker, CPickerProps } from '../picker/CPicker'
import { CTimePicker } from '../time-picker/CTimePicker'

import { useDebouncedCallback } from '../../hooks'
import { Colors } from '../../types'
import { getLocalDateFromString } from './utils'

export interface CDateRangePickerProps
  extends Omit<CFormControlWrapperProps, 'floatingLabel'>,
    Omit<CPickerProps, 'placeholder'>,
    Omit<CCalendarProps, 'onDayHover' | 'onCalendarDateChange'> {
  /**
   * The number of calendars that render on desktop devices.
   */
  calendars?: number
  /**
   * Toggle visibility or set the content of cancel button.
   *
   * @default 'Cancel'
   */
  cancelButton?: boolean | ReactNode
  /**
   * Sets the color context of the cancel button to one of CoreUI’s themed colors.
   *
   * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | string
   * @default 'primary'
   */
  cancelButtonColor?: Colors
  /**
   * Size the cancel button small or large.
   *
   * @default 'sm'
   */
  cancelButtonSize?: 'sm' | 'lg'
  /**
   * Set the cancel button variant to an outlined button or a ghost button.
   *
   * @default 'ghost'
   */
  cancelButtonVariant?: 'outline' | 'ghost'
  /**
   * A string of all className you want applied to the component.
   */
  className?: string
  /**
   * If true the dropdown will be immediately closed after submitting the full date.
   *
   * @since 4.8.0
   */
  closeOnSelect?: boolean
  /**
   * Toggle visibility or set the content of the cleaner button.
   */
  cleaner?: boolean
  /**
   * Toggle visibility or set the content of confirm button.
   *
   * @default 'OK'
   */
  confirmButton?: boolean | ReactNode
  /**
   * Sets the color context of the confirm button to one of CoreUI’s themed colors.
   *
   * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | string
   * @default 'primary'
   */
  confirmButtonColor?: Colors
  /**
   * Size the confirm button small or large.
   *
   * @default 'sm'
   */
  confirmButtonSize?: 'sm' | 'lg'
  /**
   * Set the confirm button variant to an outlined button or a ghost button.
   */
  confirmButtonVariant?: 'outline' | 'ghost'
  /**
   * Set date format.
   * We use date-fns to format dates. Visit https://date-fns.org/v2.28.0/docs/format to check accepted patterns.
   */
  format?: string
  /**
   * The id global attribute defines an identifier (ID) that must be unique in the whole document.
   *
   * The name attributes for input elements are generated based on the `id` property:
   * - \{id\}-start-date
   * - \{id\}-end-date
   */
  id?: string
  /**
   * Toggle visibility or set the content of the input indicator.
   */
  indicator?: ReactNode | boolean
  /**
   * Custom function to format the selected date into a string according to a custom format.
   *
   * @since v4.14.0
   */
  inputDateFormat?: (date: Date) => string
  /**
   * Custom function to parse the input value into a valid Date object.
   *
   * @since v4.14.0
   */
  inputDateParse?: (date: string | Date) => Date
  /**
   * Defines the delay (in milliseconds) for the input field's onChange event.
   *
   * @since v4.14.0
   */
  inputOnChangeDelay?: number
  /**
   * Toggle the readonly state for the component.
   */
  inputReadOnly?: boolean
  /**
   * Specifies short hints that are visible in start date and end date inputs.
   */
  placeholder?: string | string[]
  /**
   * @ignore
   */
  range?: boolean
  /**
   * Predefined date ranges the user can select from.
   */
  ranges?: object
  /**
   * Sets the color context of the cancel button to one of CoreUI’s themed colors.
   *
   * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | string
   */
  rangesButtonsColor?: Colors
  /**
   * Size the ranges button small or large.
   */
  rangesButtonsSize?: 'sm' | 'lg'
  /**
   * Set the ranges button variant to an outlined button or a ghost button.
   */
  rangesButtonsVariant?: 'outline' | 'ghost'
  /**
   * When present, it specifies that date must be filled out before submitting the form.
   *
   * @since 4.10.0
   */
  required?: boolean
  /**
   * Default icon or character character that separates two dates.
   */
  separator?: ReactNode | boolean
  /**
   * Size the component small or large.
   */
  size?: 'sm' | 'lg'
  /**
   * Provide an additional time selection by adding select boxes to choose times.
   */
  timepicker?: boolean
  /**
   * Toggle visibility or set the content of today button.
   *
   * @default 'Today'
   */
  todayButton?: boolean | ReactNode
  /**
   * Sets the color context of the today button to one of CoreUI’s themed colors.
   *
   * @type 'primary' | 'secondary' | 'success' | 'danger' | 'warning' | 'info' | 'dark' | 'light' | string
   * @default 'primary'
   */
  todayButtonColor?: Colors
  /**
   * Size the today button small or large.
   *
   * @default 'sm'
   */
  todayButtonSize?: 'sm' | 'lg'
  /**
   * Set the today button variant to an outlined button or a ghost button.
   */
  todayButtonVariant?: 'outline' | 'ghost'
}

export const CDateRangePicker = forwardRef<HTMLDivElement | HTMLLIElement, CDateRangePickerProps>(
  (
    {
      calendars = 2,
      calendarDate,
      cancelButton = 'Cancel',
      cancelButtonColor = 'primary',
      cancelButtonSize = 'sm',
      cancelButtonVariant = 'ghost',
      className,
      cleaner = true,
      closeOnSelect = true,
      confirmButton = 'OK',
      confirmButtonColor = 'primary',
      confirmButtonSize = 'sm',
      confirmButtonVariant,
      dayFormat,
      disabled,
      disabledDates,
      endDate,
      feedback,
      feedbackInvalid,
      feedbackValid,
      firstDayOfWeek,
      format,
      footer,
      id,
      indicator = true,
      inputDateFormat,
      inputDateParse,
      inputOnChangeDelay = 750,
      inputReadOnly,
      invalid,
      label,
      locale = 'default',
      maxDate,
      minDate,
      navigation,
      navYearFirst,
      onEndDateChange,
      onHide,
      onStartDateChange,
      onShow,
      placeholder = ['Start date', 'End date'],
      range = true,
      ranges,
      rangesButtonsColor = 'secondary',
      rangesButtonsSize,
      rangesButtonsVariant = 'ghost',
      required,
      separator = true,
      selectAdjacementDays,
      showAdjacementDays,
      size,
      startDate,
      text,
      timepicker,
      toggler,
      todayButton = 'Today',
      todayButtonColor = 'primary',
      todayButtonSize = 'sm',
      todayButtonVariant,
      tooltipFeedback,
      valid,
      visible,
      weekdayFormat,
      ...rest
    },
    ref,
  ) => {
    const inputEndRef = useRef<HTMLInputElement>(null)
    const inputStartRef = useRef<HTMLInputElement>(null)
    const formRef = useRef<HTMLFormElement>()

    const [_calendarDate, setCalendarDate] = useState<Date>(
      calendarDate ? new Date(calendarDate) : new Date(),
    )
    const [_endDate, setEndDate] = useState<Date | null>(endDate ? new Date(endDate) : null)
    const [_maxDate, setMaxDate] = useState<Date | null>(maxDate ? new Date(maxDate) : null)
    const [_minDate, setMinDate] = useState<Date | null>(minDate ? new Date(minDate) : null)
    const [_startDate, setStartDate] = useState<Date | null>(startDate ? new Date(startDate) : null)
    const [_visible, setVisible] = useState(visible)

    const [initialStartDate, setInitialStartDate] = useState<Date | null>(
      startDate ? new Date(startDate) : null,
    )
    const [initialEndDate, setInitialEndDate] = useState<Date | null>(
      endDate ? new Date(endDate) : null,
    )
    const [inputStartHoverValue, setInputStartHoverValue] = useState<Date | null>(null)
    const [inputEndHoverValue, setInputEndHoverValue] = useState<Date | null>(null)
    const [isValid, setIsValid] = useState(valid ?? (invalid === true ? false : undefined))
    const [selectEndDate, setSelectEndDate] = useState(false)

    useEffect(() => {
      setIsValid(valid ?? (invalid === true ? false : undefined))
    }, [valid, invalid])

    useEffect(() => {
      setStartDate(startDate ? new Date(startDate) : null)
      setCalendarDate(startDate ? new Date(startDate) : new Date())
    }, [startDate])

    useEffect(() => {
      setEndDate(endDate ? new Date(endDate) : null)
      range && setCalendarDate(endDate ? new Date(endDate) : new Date())
    }, [endDate])

    useEffect(() => {
      maxDate && setMaxDate(new Date(maxDate))
    }, [maxDate])

    useEffect(() => {
      minDate && setMinDate(new Date(minDate))
    }, [minDate])

    useEffect(() => {
      if (inputStartHoverValue) {
        setInputValue(inputStartRef.current, inputStartHoverValue)
        return
      }

      setInputValue(inputStartRef.current, _startDate)
    }, [inputStartHoverValue, _startDate])

    useEffect(() => {
      if (inputEndHoverValue) {
        setInputValue(inputEndRef.current, inputEndHoverValue)
        return
      }

      setInputValue(inputEndRef.current, _endDate)
    }, [inputEndHoverValue, _endDate])

    useEffect(() => {
      if (inputStartRef.current && inputStartRef.current.form) {
        formRef.current = inputStartRef.current.form
      }
    }, [inputStartRef])

    useEffect(() => {
      if (formRef.current) {
        formRef.current.addEventListener('submit', (event) => {
          setTimeout(() => handleFormValidation(event.target as HTMLFormElement))
        })

        handleFormValidation(formRef.current)
      }
    }, [formRef, _startDate, _endDate])

    const formatDate = (date: Date) => {
      return inputDateFormat
        ? inputDateFormat(date)
        : format
        ? dateFormat(date, format)
        : timepicker
        ? date.toLocaleString(locale)
        : date.toLocaleDateString(locale)
    }

    const setInputValue = (el: HTMLInputElement | null, date: Date | null) => {
      if (!el) {
        return
      }

      if (date) {
        el.value = formatDate(date)
        return
      }

      el.value = ''
    }

    const handleDayHover = (date: Date | null) => {
      selectEndDate ? setInputEndHoverValue(date) : setInputStartHoverValue(date)
    }

    const handleCalendarDateChange = (date: Date, difference?: number) => {
      difference
        ? setCalendarDate(new Date(date.getFullYear(), date.getMonth() - difference, 1))
        : setCalendarDate(date)
    }

    const handleClear = (event: React.MouseEvent<HTMLElement>) => {
      event.stopPropagation()
      setStartDate(null)
      setEndDate(null)
    }

    const handleEndDateChange = (date: Date | null) => {
      setEndDate(date)
      setInputEndHoverValue(null)
      onEndDateChange && onEndDateChange(date, date ? formatDate(date) : undefined)

      if (timepicker || footer) {
        return
      }

      if (closeOnSelect) {
        _startDate !== null && setVisible(false)
      }
    }

    const handleFormValidation = (form: HTMLFormElement) => {
      if (!form.classList.contains('was-validated')) {
        return
      }

      if ((range && _startDate && _endDate) || (!range && _startDate)) {
        return setIsValid(true)
      }

      setIsValid(false)
    }

    const handleStartDateChange = (date: Date | null) => {
      setStartDate(date)
      setInputStartHoverValue(null)
      onStartDateChange && onStartDateChange(date, date ? formatDate(date) : undefined)

      if (timepicker || footer) {
        return
      }

      if (closeOnSelect && !range) {
        setVisible(false)
      }
    }

    const handleOnChange = useDebouncedCallback((value: string, input: string) => {
      const date = inputDateParse
        ? inputDateParse(value)
        : getLocalDateFromString(value, locale, timepicker)
      if (date instanceof Date && date.getTime()) {
        setCalendarDate(date)
        input === 'start' ? setStartDate(date) : setEndDate(date)
      }
    }, inputOnChangeDelay)

    const InputGroup = () => (
      <div
        className={classNames('input-group', 'picker-input-group', {
          [`input-group-${size}`]: size,
        })}
      >
        <input
          autoComplete="off"
          className={classNames('form-control date-picker-input', {
            hover: inputStartHoverValue,
          })}
          disabled={disabled}
          {...(id && { name: range ? `${id}-start-date` : `${id}-date` })}
          placeholder={Array.isArray(placeholder) ? placeholder[0] : placeholder}
          readOnly={inputReadOnly || typeof format === 'string'}
          required={required}
          onChange={(event) => {
            handleOnChange(event.target.value, 'start')
          }}
          onClick={() => setSelectEndDate(false)}
          ref={inputStartRef}
        />
        {range && separator !== false && (
          <span className="input-group-text">
            <span className="picker-input-group-icon date-picker-arrow-icon"></span>
          </span>
        )}
        {range && (
          <input
            autoComplete="off"
            className={classNames('form-control date-picker-input', {
              hover: inputEndHoverValue,
            })}
            disabled={disabled}
            {...(id && { name: `${id}-end-date` })}
            placeholder={placeholder[1]}
            readOnly={inputReadOnly || typeof format === 'string'}
            required={required}
            onChange={(event) => {
              handleOnChange(event.target.value, 'end')
            }}
            onClick={() => setSelectEndDate(true)}
            ref={inputEndRef}
          />
        )}
        {(indicator || cleaner) && (
          <span className="input-group-text">
            {indicator && (
              <span className="picker-input-group-indicator">
                {typeof indicator === 'boolean' ? (
                  <span className="picker-input-group-icon date-picker-input-icon" />
                ) : (
                  indicator
                )}
              </span>
            )}
            {cleaner && (_startDate || _endDate) && (
              <span
                className="picker-input-group-cleaner"
                role="button"
                onClick={(event) => handleClear(event)}
              >
                {typeof cleaner === 'boolean' ? (
                  <span className="picker-input-group-icon date-picker-cleaner-icon" />
                ) : (
                  cleaner
                )}
              </span>
            )}
          </span>
        )}
      </div>
    )

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
            'date-picker',
            {
              [`date-picker-${size}`]: size,
              disabled: disabled,
              'is-invalid': isValid === false ? true : false,
              'is-valid': isValid,
            },
            className,
          )}
          disabled={disabled}
          footer={footer || timepicker}
          footerContent={
            <div className="picker-footer">
              {todayButton && (
                <CButton
                  className="me-auto"
                  color={todayButtonColor}
                  size={todayButtonSize}
                  variant={todayButtonVariant}
                  onClick={() => {
                    const date = new Date()
                    handleStartDateChange(date)
                    range && handleEndDateChange(date)
                    setCalendarDate(date)
                  }}
                >
                  {todayButton}
                </CButton>
              )}
              {cancelButton && (
                <CButton
                  color={cancelButtonColor}
                  size={cancelButtonSize}
                  variant={cancelButtonVariant}
                  onClick={() => {
                    handleStartDateChange(initialStartDate)
                    range && handleEndDateChange(initialEndDate)
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
          toggler={toggler ?? InputGroup()}
          onHide={() => {
            setVisible(false)
            onHide && onHide()
          }}
          onShow={() => {
            setInitialStartDate(_startDate)
            setInitialEndDate(_endDate)
            setVisible(true)
            onShow && onShow()
          }}
          visible={_visible}
          {...rest}
          ref={ref}
        >
          <div className="date-picker-body">
            {ranges && (
              <div className="date-picker-ranges">
                {Object.keys(ranges).map((key: string, index: number) => (
                  <CButton
                    color={rangesButtonsColor}
                    key={index}
                    onClick={() => {
                      handleStartDateChange(ranges[key][0])
                      handleEndDateChange(ranges[key][1])
                    }}
                    size={rangesButtonsSize}
                    variant={rangesButtonsVariant}
                  >
                    {key}
                  </CButton>
                ))}
              </div>
            )}
            <CCalendar
              calendarDate={_calendarDate}
              calendars={isMobile ? 1 : calendars}
              className="date-picker-calendars"
              dayFormat={dayFormat}
              disabledDates={disabledDates}
              endDate={_endDate}
              firstDayOfWeek={firstDayOfWeek}
              locale={locale}
              maxDate={_maxDate}
              minDate={_minDate}
              navigation={navigation}
              navYearFirst={navYearFirst}
              range={range}
              selectAdjacementDays={selectAdjacementDays}
              selectEndDate={selectEndDate}
              showAdjacementDays={showAdjacementDays}
              startDate={_startDate}
              onDayHover={(date) => handleDayHover(date)}
              onCalendarDateChange={(date) => handleCalendarDateChange(date)}
              onStartDateChange={(date) => handleStartDateChange(date)}
              onEndDateChange={(date) => handleEndDateChange(date)}
              onSelectEndChange={(value) => setSelectEndDate(value)}
              weekdayFormat={weekdayFormat}
            />
            {timepicker && (
              <div className="date-picker-timepickers">
                {isMobile || (range && calendars === 1) ? (
                  <>
                    <CTimePicker
                      container="inline"
                      disabled={_startDate === null ? true : false}
                      locale={locale}
                      onTimeChange={(_, __, date) => date && handleStartDateChange(date)}
                      time={_startDate}
                      variant="select"
                    />
                    <CTimePicker
                      container="inline"
                      disabled={_endDate === null ? true : false}
                      locale={locale}
                      onTimeChange={(_, __, date) => date && handleEndDateChange(date)}
                      time={_endDate}
                      variant="select"
                    />
                  </>
                ) : (
                  Array.from({ length: calendars }).map((_, index) => (
                    <CTimePicker
                      container="inline"
                      disabled={
                        index === 0
                          ? _startDate === null
                            ? true
                            : false
                          : _endDate === null
                          ? true
                          : false
                      }
                      key={index}
                      locale={locale}
                      onTimeChange={(_, __, date) =>
                        index === 0
                          ? date && handleStartDateChange(date)
                          : date && handleEndDateChange(date)
                      }
                      time={index === 0 ? _startDate : _endDate}
                      variant="select"
                    />
                  ))
                )}
              </div>
            )}
          </div>
        </CPicker>
      </CFormControlWrapper>
    )
  },
)

CDateRangePicker.displayName = 'CDateRangePicker'

CDateRangePicker.propTypes = {
  ...CCalendar.propTypes,
  ...CFormControlWrapper.propTypes,
  ...CPicker.propTypes,
  cancelButton: PropTypes.oneOfType([PropTypes.bool, PropTypes.node]),
  cancelButtonColor: CButton.propTypes?.color,
  cancelButtonSize: CButton.propTypes?.size,
  cancelButtonVariant: CButton.propTypes?.variant,
  calendars: PropTypes.number,
  className: PropTypes.string,
  cleaner: PropTypes.bool,
  closeOnSelect: PropTypes.bool,
  confirmButton: PropTypes.oneOfType([PropTypes.bool, PropTypes.node]),
  confirmButtonColor: CButton.propTypes?.color,
  confirmButtonSize: CButton.propTypes?.size,
  confirmButtonVariant: CButton.propTypes?.variant,
  id: PropTypes.string,
  indicator: PropTypes.oneOfType([PropTypes.bool, PropTypes.node]),
  inputDateFormat: PropTypes.func,
  inputDateParse: PropTypes.func,
  inputOnChangeDelay: PropTypes.number,
  inputReadOnly: PropTypes.bool,
  placeholder: PropTypes.oneOfType([
    PropTypes.string,
    PropTypes.arrayOf(PropTypes.string.isRequired),
  ]),
  range: PropTypes.bool,
  ranges: PropTypes.object,
  rangesButtonsColor: CButton.propTypes?.color,
  rangesButtonsSize: CButton.propTypes?.size,
  rangesButtonsVariant: CButton.propTypes?.variant,
  required: PropTypes.bool,
  separator: PropTypes.oneOfType([PropTypes.bool, PropTypes.node]),
  size: PropTypes.oneOf(['sm', 'lg']),
  timepicker: PropTypes.bool,
  todayButton: PropTypes.oneOfType([PropTypes.bool, PropTypes.node]),
  todayButtonColor: CButton.propTypes?.color,
  todayButtonSize: CButton.propTypes?.size,
  todayButtonVariant: CButton.propTypes?.variant,
}
