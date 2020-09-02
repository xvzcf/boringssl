// TODO(xvzcf) : The code here has been haphazardly taken from musl libc
// and from crypto/asn1. A discussion on how to obviate this is needed.

#include <limits.h>

/* 2000-03-01 (mod 400 year, immediately after feb29 */
#define LEAPOCH (946684800LL + 86400 * (31 + 29))

#define DAYS_PER_400Y (365 * 400 + 97)
#define DAYS_PER_100Y (365 * 100 + 24)
#define DAYS_PER_4Y (365 * 4 + 1)

static long long year_to_secs(long long year, int *is_leap) {
  if (year - 2ULL <= 136) {
    int y = year;
    int leaps = (y - 68) >> 2;
    if (!((y - 68) & 3)) {
      leaps--;
      if (is_leap)
        *is_leap = 1;
    } else if (is_leap)
      *is_leap = 0;
    return 31536000 * (y - 70) + 86400 * leaps;
  }

  int cycles, centuries, leaps, rem;

  int array[1] = {0};
  if (!is_leap)
    is_leap = &array[0];
  cycles = (year - 100) / 400;
  rem = (year - 100) % 400;
  if (rem < 0) {
    cycles--;
    rem += 400;
  }
  if (!rem) {
    *is_leap = 1;
    centuries = 0;
    leaps = 0;
  } else {
    if (rem >= 200) {
      if (rem >= 300)
        centuries = 3, rem -= 300;
      else
        centuries = 2, rem -= 200;
    } else {
      if (rem >= 100)
        centuries = 1, rem -= 100;
      else
        centuries = 0;
    }
    if (!rem) {
      *is_leap = 0;
      leaps = 0;
    } else {
      leaps = rem / 4U;
      rem %= 4U;
      *is_leap = !rem;
    }
  }

  leaps += 97 * cycles + 24 * centuries - *is_leap;

  return (year - 100) * 31536000LL + leaps * 86400LL + 946684800 + 86400;
}

static int month_to_secs(int month, int is_leap) {
  static const int secs_through_month[] = {
      0,           31 * 86400,  59 * 86400,  90 * 86400,
      120 * 86400, 151 * 86400, 181 * 86400, 212 * 86400,
      243 * 86400, 273 * 86400, 304 * 86400, 334 * 86400};
  int t = secs_through_month[month];
  if (is_leap && month >= 2)
    t += 86400;
  return t;
}

static long long tm_to_secs(const struct tm *tm) {
  int is_leap;
  long long year = tm->tm_year;
  int month = tm->tm_mon;
  if (month >= 12 || month < 0) {
    int adj = month / 12;
    month %= 12;
    if (month < 0) {
      adj--;
      month += 12;
    }
    year += adj;
  }
  long long t = year_to_secs(year, &is_leap);
  t += month_to_secs(month, is_leap);
  t += 86400LL * (tm->tm_mday - 1);
  t += 3600LL * tm->tm_hour;
  t += 60LL * tm->tm_min;
  t += tm->tm_sec;
  return t;
}


static int secs_to_tm(long long t, struct tm *tm) {
  long long days, secs, years;
  int remdays, remsecs, remyears;
  int qc_cycles, c_cycles, q_cycles;
  int months;
  int wday, yday, leap;
  static const char days_in_month[] = {31, 30, 31, 30, 31, 31,
                                       30, 31, 30, 31, 31, 29};

  /* Reject time_t values whose year would overflow int */
  if (t < INT_MIN * 31622400LL || t > INT_MAX * 31622400LL)
    return -1;

  secs = t - LEAPOCH;
  days = secs / 86400;
  remsecs = secs % 86400;
  if (remsecs < 0) {
    remsecs += 86400;
    days--;
  }

  wday = (3 + days) % 7;
  if (wday < 0)
    wday += 7;

  qc_cycles = days / DAYS_PER_400Y;
  remdays = days % DAYS_PER_400Y;
  if (remdays < 0) {
    remdays += DAYS_PER_400Y;
    qc_cycles--;
  }

  c_cycles = remdays / DAYS_PER_100Y;
  if (c_cycles == 4)
    c_cycles--;
  remdays -= c_cycles * DAYS_PER_100Y;

  q_cycles = remdays / DAYS_PER_4Y;
  if (q_cycles == 25)
    q_cycles--;
  remdays -= q_cycles * DAYS_PER_4Y;

  remyears = remdays / 365;
  if (remyears == 4)
    remyears--;
  remdays -= remyears * 365;

  leap = !remyears && (q_cycles || !c_cycles);
  yday = remdays + 31 + 28 + leap;
  if (yday >= 365 + leap)
    yday -= 365 + leap;

  years = remyears + 4 * q_cycles + 100 * c_cycles + 400LL * qc_cycles;

  for (months = 0; days_in_month[months] <= remdays; months++)
    remdays -= days_in_month[months];

  if (months >= 10) {
    months -= 12;
    years++;
  }

  if (years + 100 > INT_MAX || years + 100 < INT_MIN)
    return -1;

  tm->tm_year = years + 100;
  tm->tm_mon = months + 2;
  tm->tm_mday = remdays + 1;
  tm->tm_wday = wday;
  tm->tm_yday = yday;

  tm->tm_hour = remsecs / 3600;
  tm->tm_min = remsecs / 60 % 60;
  tm->tm_sec = remsecs % 60;

  return 0;
}

static long long asn1_generalizedtime_to_unix_timestamp(const uint8_t *in,
                                                        const size_t in_len) {
  static const int min[9] = {0, 0, 1, 1, 0, 0, 0, 0, 0};
  static const int max[9] = {99, 99, 12, 31, 23, 59, 59, 12, 59};
  char *a;
  int n, i;

  size_t l = in_len;
  a = (char *)in;
  size_t o = 0;
  struct tm tm, tm_check;

  /*
   * GENERALIZEDTIME is similar to UTCTIME except the year is represented
   * as YYYY. This stuff treats everything as a two digit field so make
   * first two fields 00 to 99
   */
  if (l < 13)
    return 0;
  for (i = 0; i < 7; i++) {
    /* According to rfc5280#section-4.1.2.5.2, UTCTime values MUST
     * be expressed in Greenwich Mean Time (Zulu)
     */
    if ((i == 6) && (a[o] == 'Z')) {
      i++;
      tm.tm_sec = 0;
      break;
    }
    if ((a[o] < '0') || (a[o] > '9'))
      return 0;
    n = a[o] - '0';
    if (++o > l)
      return 0;

    if ((a[o] < '0') || (a[o] > '9'))
      return 0;

    n = (n * 10) + a[o] - '0';

    if (++o > l)
      return 0;

    if ((n < min[i]) || (n > max[i]))
      return 0;

    switch (i) {
      case 0:
        tm.tm_year = n * 100 - 1900;
        break;
      case 1:
        tm.tm_year += n;
        break;
      case 2:
        tm.tm_mon = n - 1;
        break;
      case 3:
        tm.tm_mday = n;
        break;
      case 4:
        tm.tm_hour = n;
        break;
      case 5:
        tm.tm_min = n;
        break;
      case 6:
        tm.tm_sec = n;
        break;
    }
  }
  /*
   * https://tools.ietf.org/html/rfc5280#section-4.1.2.5.1 says that
   * GeneralizedTime values MUST NOT include fractional seconds
   */
  if (a[o] == '.') {
    return 0;
  }

  if (a[o] == 'Z') {
    o++;
  } else {
    return 0;
  }
  if (o != l) {
    return 0;
  }

  long long t = tm_to_secs(&tm);
  if (secs_to_tm(t, &tm_check) < 0) {
    return 0;
  }

  return t;
}

static long long asn1_utctime_to_unix_timestamp(const uint8_t *in,
                                                const size_t in_len) {
  static const int min[8] = {0, 1, 1, 0, 0, 0, 0, 0};
  static const int max[8] = {99, 12, 31, 23, 59, 59, 12, 59};
  int n, i;

  size_t l = in_len;
  char *a = (char *)in;
  size_t o = 0;
  struct tm tm, tm_check;

  if (l < 11)
    return 0;
  for (i = 0; i < 6; i++) {
    /* According to rfc5280#section-4.1.2.5.1, UTCTime values MUST
     * be expressed in Greenwich Mean Time (Zulu)
     */
    if ((i == 5) && (a[o] == 'Z')) {
      i++;
      tm.tm_sec = 0;
      break;
    }
    if ((a[o] < '0') || (a[o] > '9'))
      return 0;
    n = a[o] - '0';
    if (++o > l)
      return 0;

    if ((a[o] < '0') || (a[o] > '9'))
      return 0;
    n = (n * 10) + a[o] - '0';
    if (++o > l)
      return 0;

    if ((n < min[i]) || (n > max[i]))
      return 0;
    switch (i) {
      case 0:
        tm.tm_year = n < 50 ? n + 100 : n;
        break;
      case 1:
        tm.tm_mon = n - 1;
        break;
      case 2:
        tm.tm_mday = n;
        break;
      case 3:
        tm.tm_hour = n;
        break;
      case 4:
        tm.tm_min = n;
        break;
      case 5:
        tm.tm_sec = n;
        break;
    }
  }
  if (a[o] == 'Z')
    o++;
  else
    return 0;
  if (o != l)
    return 0;

  long long t = tm_to_secs(&tm);
  if (secs_to_tm(t, &tm_check) < 0) {
    return 0;
  }

  return t;
}
