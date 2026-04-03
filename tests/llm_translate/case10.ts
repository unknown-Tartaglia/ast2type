function charFrequency(str: string): Record<string, number> {
  if (typeof str !== 'string') {
    return {};
  }

  const frequency: Record<string, number> = {};

  for (let i = 0; i < str.length; i++) {
    const char = str[i];
    if (char === ' ') continue; // Skip spaces

    if (frequency[char]) {
      frequency[char]++;
    } else {
      frequency[char] = 1;
    }
  }

  return frequency;
}

module.exports = charFrequency;