function daysBetween(date1, date2) {
  if (typeof date1 !== 'string' || typeof date2 !== 'string') {
    return null;
  }

  const regex = /^\d{4}-\d{2}-\d{2}$/;
  if (!regex.test(date1) || !regex.test(date2)) {
    return null;
  }

  try {
    const d1 = new Date(date1 + 'T00:00:00');
    const d2 = new Date(date2 + 'T00:00:00');

    if (isNaN(d1.getTime()) || isNaN(d2.getTime())) {
      return null;
    }

    const timeDiff = Math.abs(d2.getTime() - d1.getTime());
    const daysDiff = Math.floor(timeDiff / (1000 * 60 * 60 * 24));
    return daysDiff;
  } catch (e) {
    return null;
  }
}

module.exports = daysBetween;