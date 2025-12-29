import type { LocalizedTimePartials } from './types'

export const convert12hTo24h = (abbr: 'am' | 'pm', hour: number) => {
  if (abbr === 'am' && hour === 12) {
    return 0
  }
  if (abbr === 'am') {
    return hour
  }
  if (abbr === 'pm' && hour === 12) {
    return 12
  }
  return hour + 12
}

export const convert24hTo12h = (hour: number) => hour % 12 || 12

export const convertTimeToDate = (time: Date | string | null | undefined) =>
  time ? (time instanceof Date ? new Date(time) : new Date(`1970-01-01 ${time}`)) : null

export const getAmPm = (date: Date, locale: string) => {
  if (date.toLocaleTimeString(locale).includes('AM')) {
    return 'am'
  }
  if (date.toLocaleTimeString(locale).includes('PM')) {
    return 'pm'
  }
  return date.getHours() >= 12 ? 'pm' : 'am'
}

// TODO: clean-up
export const getListOfHours = (locale: string, ampm: 'auto' | boolean = 'auto') =>
  Array.from({ length: (ampm === 'auto' && isAmPm(locale)) || ampm === true ? 12 : 24 }, (_, i) => {
    return {
      value: (ampm === 'auto' && isAmPm(locale)) || ampm === true ? i + 1 : i,
      label: ((ampm === 'auto' && isAmPm(locale)) || ampm === true ? i + 1 : i).toLocaleString(
        locale,
      ),
    }
  })

// TODO: clean-up
export const getListOfMinutes = (locale: string, valueAsString = false) =>
  Array.from({ length: 60 }, (_, i) => {
    const d = new Date()
    d.setMinutes(i)
    return {
      value: valueAsString ? i.toString() : i,
      label: d
        .toLocaleTimeString(locale, {
          minute: '2-digit',
          second: '2-digit',
        })
        .split(/[^A-Za-z0-9\u06F0-\u06F90-9]/)[0],
    }
  })

// TODO: clean-up
export const getListOfSeconds = (locale: string, valueAsString = false) =>
  Array.from({ length: 60 }, (_, i) => {
    const d = new Date()
    d.setSeconds(i)
    return {
      value: valueAsString ? i.toString() : i,
      label: d
        .toLocaleTimeString(locale, {
          minute: '2-digit',
          second: '2-digit',
        })
        .split(/[^A-Za-z0-9\u06F0-\u06F90-9]/)[0],
    }
  })

export const getLocalizedTimePartials = (
  locale: string,
  ampm: 'auto' | boolean = 'auto',
): LocalizedTimePartials => {
  const date = new Date()
  const hour12 = ['am', 'AM', 'pm', 'PM'].some((el) => date.toLocaleString(locale).includes(el))
  const listOfHours = Array.from(
    { length: (ampm === 'auto' && hour12) || ampm === true ? 12 : 24 },
    (_, i) => {
      return {
        value: (ampm === 'auto' && hour12) || ampm === true ? i + 1 : i,
        label: ((ampm === 'auto' && hour12) || ampm === true ? i + 1 : i).toLocaleString(locale),
      }
    },
  )
  const listOfMinutesSeconds = Array.from({ length: 60 }, (_, i) => {
    date.setMinutes(i)
    return {
      value: i,
      label: date
        .toLocaleTimeString(locale, {
          minute: '2-digit',
          second: '2-digit',
        })
        .split(/[^A-Za-z0-9\u06F0-\u06F90-9]/)[0],
    }
  })

  return {
    listOfHours,
    listOfMinutes: listOfMinutesSeconds,
    listOfSeconds: listOfMinutesSeconds,
    hour12,
  }
}

export const getSelectedHour = (
  date: Date | null,
  locale: string,
  ampm: 'auto' | boolean = 'auto',
) =>
  date
    ? (ampm === 'auto' && isAmPm(locale)) || ampm === true
      ? convert24hTo12h(date.getHours())
      : date.getHours()
    : ''

export const getSelectedMinutes = (date: Date | null) => (date ? date.getMinutes() : '')

export const getSelectedSeconds = (date: Date | null) => (date ? date.getSeconds() : '')

export const isAmPm = (locale: string) =>
  ['am', 'AM', 'pm', 'PM'].some((el) => new Date().toLocaleString(locale).includes(el))

export const isValidTime = (time: string) => {
  const d = new Date(`1970-01-01 ${time}`)
  return d instanceof Date && d.getTime()
}
