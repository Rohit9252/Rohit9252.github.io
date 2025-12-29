import React, {
  FormEvent,
  forwardRef,
  HTMLAttributes,
  ReactNode,
  useEffect,
  useState,
  useRef,
  useMemo,
} from 'react'

import classNames from 'classnames'
import PropTypes from 'prop-types'

import type { Placement } from '@popperjs/core'

import { CFormControlWrapper, CFormControlWrapperProps } from '../form/CFormControlWrapper'

import { CMultiSelectNativeSelect } from './CMultiSelectNativeSelect'
import { CMultiSelectOptions } from './CMultiSelectOptions'
import { CMultiSelectSelection } from './CMultiSelectSelection'

import { useForkedRef, usePopper } from '../../hooks'
import { isRTL } from '../../utils'
import { createOption, filterOptionsList, flattenOptionsArray, selectOptions } from './utils'
import type { Option, OptionsGroup, SelectedOption } from './types'

export interface CMultiSelectProps
  extends Omit<CFormControlWrapperProps, 'floatingClassName' | 'floatingLabel'>,
    Omit<HTMLAttributes<HTMLDivElement>, 'onChange'> {
  /**
   * Allow users to create options if they are not in the list of options.
   *
   * @since 4.11.0
   */
  allowCreateOptions?: boolean
  /**
   * A string of all className you want applied to the base component.
   */
  className?: string
  /**
   * Enables selection cleaner element.
   */
  cleaner?: boolean
  /**
   * Clear current search on selecting an item.
   *
   * @since 4.11.0
   */
  clearSearchOnSelect?: boolean
  /**
   * Toggle the disabled state for the component.
   */
  disabled?: boolean
  /**
   * The id global attribute defines an identifier (ID) that must be unique in the whole document.
   *
   * The name and id attributes for the native select element are generated based on the `id` property:
   * - <select id="\{id\}-multi-select" name="\{id\}-multi-select" />
   */
  id?: string
  /**
   * When set, the options list will have a loading style: loading spinner and reduced opacity.
   *
   * @since 4.11.0
   */
  loading?: boolean
  /**
   * It specifies that multiple options can be selected at once.
   */
  multiple?: boolean
  /**
   * Execute a function when a user changes the selected option.
   */
  onChange?: (selected: Option[]) => void
  /**
   * Execute a function when the filter value changed.
   *
   * @since 4.8.0
   */
  onFilterChange?: (value: string) => void
  /**
   * The callback is fired when the Multi Select component requests to be hidden.
   */
  onHide?: () => void
  /**
   * The callback is fired when the Multi Select component requests to be shown.
   */
  onShow?: () => void
  /**
   * List of option elements.
   */
  options: (Option | OptionsGroup)[]
  /**
   * Sets maxHeight of options list.
   */
  optionsMaxHeight?: number | string
  /**
   * Sets option style.
   */
  optionsStyle?: 'checkbox' | 'text'
  /**
   * Custom template for options.
   *
   * @since 4.12.0
   */
  optionsTemplate?: (option: Option) => ReactNode
  /**
   * Custom template for options groups.
   *
   * @since 4.12.0
   */
  optionsGroupsTemplate?: (option: OptionsGroup) => ReactNode
  /**
   * Specifies a short hint that is visible in the search input.
   */
  placeholder?: string
  /**
   * When it is present, it indicates that the user must choose a value before submitting the form.
   */
  required?: boolean
  /**
   * Enables search input element.
   */
  search?: boolean | 'external'
  /**
   * Sets the label for no results when filtering.
   */
  searchNoResultsLabel?: string | ReactNode
  /**
   * Enables select all button.
   */
  selectAll?: boolean
  /**
   * Sets the select all button label.
   */
  selectAllLabel?: string | ReactNode
  /**
   * Sets the selection style.
   */
  selectionType?: 'counter' | 'tags' | 'text'
  /**
   * Sets the counter selection label.
   */
  selectionTypeCounterText?: string
  /**
   * Size the component small or large.
   */
  size?: 'sm' | 'lg'
  /**
   * Enable virtual scroller for the options list.
   *
   * @since 4.8.0
   */
  virtualScroller?: boolean
  /**
   * Toggle the visibility of multi select dropdown.
   */
  visible?: boolean
  /**
   * Amount of visible items when virtualScroller is set to `true`.
   *
   * @since 4.8.0
   */
  visibleItems?: number
}

export const CMultiSelect = forwardRef<HTMLDivElement, CMultiSelectProps>(
  (
    {
      allowCreateOptions,
      className,
      cleaner = true,
      clearSearchOnSelect,
      disabled,
      feedback,
      feedbackInvalid,
      feedbackValid,
      loading,
      multiple = true,
      id,
      invalid,
      label,
      onChange,
      onFilterChange,
      onHide,
      onShow,
      options,
      optionsMaxHeight = 'auto',
      optionsStyle = 'checkbox',
      optionsTemplate,
      optionsGroupsTemplate,
      placeholder = 'Select...',
      required,
      search = true,
      searchNoResultsLabel = 'No results found',
      selectAll = true,
      selectAllLabel = 'Select all options',
      selectionType = 'tags',
      selectionTypeCounterText = 'item(s) selected',
      size,
      text,
      tooltipFeedback,
      valid,
      virtualScroller,
      visible = false,
      visibleItems = 10,
      ...rest
    },
    ref,
  ) => {
    const multiSelectRef = useRef<HTMLDivElement>(null)
    const multiSelectForkedRef = useForkedRef(ref, multiSelectRef)

    const dropdownRef = useRef<HTMLDivElement>(null)
    const nativeSelectRef = useRef<HTMLSelectElement>(null)
    const togglerRef = useRef<HTMLDivElement>(null)
    const searchRef = useRef<HTMLInputElement>(null)
    const isInitialMount = useRef(true)

    const { popper, initPopper, destroyPopper } = usePopper()

    const [_options, setOptions] = useState<(Option | OptionsGroup)[]>(options)
    const [_visible, setVisible] = useState(visible)
    const [searchValue, setSearchValue] = useState('')
    const [selected, setSelected] = useState<SelectedOption[]>([])
    const [userOptions, setUserOptions] = useState<Option[]>([])

    const filteredOptions = useMemo(
      () =>
        flattenOptionsArray(
          search === 'external'
            ? [..._options, ...filterOptionsList(searchValue, userOptions)]
            : filterOptionsList(searchValue, [..._options, ...userOptions]),
          true,
        ),
      [_options, searchValue, userOptions],
    )

    const flattenedOptions = useMemo(() => flattenOptionsArray(options), [JSON.stringify(options)])

    const userOption = useMemo(() => {
      if (
        allowCreateOptions &&
        filteredOptions.some(
          (option) => option.text && option.text.toLowerCase() === searchValue.toLowerCase(),
        )
      ) {
        return false
      }

      return searchRef.current && createOption(String(searchValue), flattenedOptions)
    }, [filteredOptions, searchValue])

    const popperConfig = {
      placement: (isRTL(multiSelectRef.current) ? 'bottom-end' : 'bottom-start') as Placement,
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
      setOptions(options)

      const _selected = flattenedOptions.filter((option: Option) => option.selected === true)
      const deselected = flattenedOptions.filter(
        (option: Option) => option.selected === false,
      ) as Option[]

      _selected && setSelected(selectOptions(_selected, selected, deselected))
    }, [JSON.stringify(options)])

    useEffect(() => {
      !isInitialMount.current && onFilterChange && onFilterChange(searchValue)
    }, [searchValue])

    useEffect(() => {
      if (!isInitialMount.current && nativeSelectRef.current) {
        nativeSelectRef.current.dispatchEvent(new Event('change', { bubbles: true }))
      }

      if (popper) {
        popper.update()
      }
    }, [JSON.stringify(selected)])

    useEffect(() => {
      if (_visible) {
        onShow && onShow()

        window.addEventListener('mouseup', handleMouseUp)
        window.addEventListener('keyup', handleKeyUp)

        togglerRef.current &&
          dropdownRef.current &&
          initPopper(togglerRef.current, dropdownRef.current, popperConfig)
        searchRef.current && searchRef.current.focus()
      }

      return () => {
        onHide && onHide()

        window.removeEventListener('mouseup', handleMouseUp)
        window.removeEventListener('keyup', handleKeyUp)

        destroyPopper()
      }
    }, [_visible])

    useEffect(() => {
      isInitialMount.current = false
    }, [])

    const handleKeyUp = (event: KeyboardEvent) => {
      if (event.key === 'Escape') {
        setVisible(false)
      }
    }

    const handleMouseUp = (event: Event) => {
      if (multiSelectRef.current && multiSelectRef.current.contains(event.target as HTMLElement)) {
        return
      }

      setVisible(false)
    }

    const handleSearchChange = (event: FormEvent<HTMLInputElement>) => {
      const value = (event.target as HTMLInputElement).value
      setSearchValue(value)
    }

    const handleSearchKeyDown = (event: React.KeyboardEvent<HTMLInputElement>) => {
      if (event.key === 'Enter' && searchValue && allowCreateOptions) {
        event.preventDefault()

        if (userOption) {
          setSelected([...selected, ...userOption])
          setUserOptions([...userOptions, ...userOption])
        }

        if (!userOption) {
          setSelected([
            ...selected,
            filteredOptions.find(
              (option) => String(option.text).toLowerCase() === searchValue.toLowerCase(),
            ) as Option,
          ])
        }

        setSearchValue('')
        if (searchRef.current) {
          searchRef.current.value = ''
        }

        return
      }

      if (searchValue.length > 0) {
        return
      }

      if (event.key === 'Backspace' || event.key === 'Delete') {
        const last = selected.filter((option: Option) => !option.disabled).pop()
        last && setSelected(selected.filter((option: Option) => option.value !== last.value))
      }
    }

    const handleOptionOnClick = (option: Option) => {
      if (!multiple) {
        setSelected([option] as SelectedOption[])
        setVisible(false)
        setSearchValue('')
        if (searchRef.current) {
          searchRef.current.value = ''
        }

        return
      }

      if (option.custom && !userOptions.some((_option) => _option.value === option.value)) {
        setUserOptions([...userOptions, option])
      }

      if (clearSearchOnSelect || option.custom) {
        setSearchValue('')
        if (searchRef.current) {
          searchRef.current.value = ''
          searchRef.current.focus()
        }
      }

      if (selected.some((_option) => _option.value === option.value)) {
        setSelected(selected.filter((_option) => _option.value !== option.value))
      } else {
        setSelected([...selected, option] as SelectedOption[])
      }
    }

    const handleSelectAll = () => {
      setSelected(
        selectOptions(
          [...flattenedOptions.filter((option: Option) => !option.disabled), ...userOptions],
          selected,
        ),
      )
    }

    const handleDeselectAll = () => {
      setSelected(selected.filter((option) => option.disabled))
    }

    return (
      <CFormControlWrapper
        describedby={rest['aria-describedby']}
        feedback={feedback}
        feedbackInvalid={feedbackInvalid}
        feedbackValid={feedbackValid}
        id={id}
        invalid={invalid}
        label={label}
        text={text}
        tooltipFeedback={tooltipFeedback}
        valid={valid}
      >
        <CMultiSelectNativeSelect
          className='form-multi-select'
          id={id}
          multiple={multiple}
          options={selected}
          required={required}
          value={
            multiple
              ? selected.map((option: SelectedOption) => option.value.toString())
              : selected.map((option: SelectedOption) => option.value)[0]
          }
          onChange={() => onChange && onChange(selected)}
          ref={nativeSelectRef}
        />
        <div
          className={classNames(
            'form-multi-select',
            {
              'form-multi-select-with-cleaner': cleaner,
              [`form-multi-select-${size}`]: size,
              'form-multi-select-selection-tags': multiple && selectionType === 'tags',
              disabled,
              'is-invalid': invalid,
              'is-valid': valid,
              show: _visible,
            },
            className,
          )}
          aria-expanded={_visible}
          id={id}
          ref={multiSelectForkedRef}
        >
          <div
            className="form-multi-select-input-group"
            onClick={() => setVisible(true)}
            ref={togglerRef}
          >
            <CMultiSelectSelection
              multiple={multiple}
              onRemove={(option) => !disabled && handleOptionOnClick(option)}
              placeholder={placeholder}
              search={search}
              selected={selected}
              selectionType={selectionType}
              selectionTypeCounterText={selectionTypeCounterText}
            >
              {search && (
                <input
                  type="text"
                  className="form-multi-select-search"
                  disabled={disabled}
                  autoComplete="off"
                  onChange={handleSearchChange}
                  onKeyDown={handleSearchKeyDown}
                  {...(selected.length === 0 && { placeholder: placeholder })}
                  {...(selected.length > 0 &&
                    selectionType === 'counter' && {
                      placeholder: `${selected.length} ${selectionTypeCounterText}`,
                    })}
                  {...(selected.length > 0 &&
                    !multiple && { placeholder: selected.map((option) => option.text)[0] })}
                  {...(multiple &&
                    selected.length > 0 &&
                    selectionType !== 'counter' && { size: searchValue.length + 2 })}
                  ref={searchRef}
                ></input>
              )}
            </CMultiSelectSelection>
            {!disabled && cleaner && selected.length > 0 && (
              <button
                type="button"
                className="form-multi-select-selection-cleaner"
                onClick={() => handleDeselectAll()}
              ></button>
            )}
          </div>
          <div className="form-multi-select-dropdown" role="menu" ref={dropdownRef}>
            {multiple && selectAll && (
              <button
                type="button"
                className="form-multi-select-all"
                onClick={() => handleSelectAll()}
              >
                {selectAllLabel}
              </button>
            )}
            <CMultiSelectOptions
              handleOptionOnClick={(option) => !disabled && handleOptionOnClick(option)}
              loading={loading}
              options={
                filteredOptions.length === 0 && allowCreateOptions
                  ? userOption || []
                  : filteredOptions
              }
              optionsMaxHeight={optionsMaxHeight}
              optionsStyle={optionsStyle}
              optionsTemplate={optionsTemplate}
              optionsGroupsTemplate={optionsGroupsTemplate}
              searchNoResultsLabel={searchNoResultsLabel}
              selected={selected}
              virtualScroller={virtualScroller}
              visibleItems={visibleItems}
            />
          </div>
        </div>
      </CFormControlWrapper>
    )
  },
)

CMultiSelect.propTypes = {
  className: PropTypes.string,
  cleaner: PropTypes.bool,
  clearSearchOnSelect: PropTypes.bool,
  disabled: PropTypes.bool,
  loading: PropTypes.bool,
  multiple: PropTypes.bool,
  onChange: PropTypes.func,
  onFilterChange: PropTypes.func,
  onHide: PropTypes.func,
  onShow: PropTypes.func,
  options: PropTypes.array.isRequired,
  optionsMaxHeight: PropTypes.oneOfType([PropTypes.number, PropTypes.string]),
  optionsStyle: PropTypes.oneOf(['checkbox', 'text']),
  optionsTemplate: PropTypes.func,
  optionsGroupsTemplate: PropTypes.func,
  placeholder: PropTypes.string,
  required: PropTypes.bool,
  search: PropTypes.oneOfType([PropTypes.bool, PropTypes.oneOf<'external'>(['external'])]),
  searchNoResultsLabel: PropTypes.oneOfType([PropTypes.string, PropTypes.node]),
  selectAll: PropTypes.bool,
  selectAllLabel: PropTypes.oneOfType([PropTypes.string, PropTypes.node]),
  selectionType: PropTypes.oneOf(['counter', 'tags', 'text']),
  selectionTypeCounterText: PropTypes.string,
  size: PropTypes.oneOf(['sm', 'lg']),
  virtualScroller: PropTypes.bool,
  visible: PropTypes.bool,
  visibleItems: PropTypes.number,
  ...CFormControlWrapper.propTypes,
}

CMultiSelect.displayName = 'CMultiSelect'
