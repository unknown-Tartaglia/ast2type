interface User {
  username?: string;
  age?: number;
  email?: string;
}

interface ValidationResult {
  valid: boolean;
  errors: string[];
}

function validateUser(user: any): ValidationResult {
  if (!user || typeof user !== 'object') {
    return { valid: false, errors: ['User must be an object'] };
  }

  const errors: string[] = [];

  if (!user.username || typeof user.username !== 'string') {
    errors.push('Username is required and must be a string');
  } else if (user.username.length < 3) {
    errors.push('Username must be at least 3 characters long');
  }

  if (user.age !== undefined) {
    if (typeof user.age !== 'number') {
      errors.push('Age must be a number if provided');
    } else if (user.age < 0 || user.age > 150) {
      errors.push('Age must be between 0 and 150');
    }
  }

  if (user.email !== undefined && typeof user.email !== 'string') {
    errors.push('Email must be a string if provided');
  } else if (user.email && !user.email.includes('@')) {
    errors.push('Email must contain @ symbol');
  }

  const valid = errors.length === 0;
  return { valid, errors: valid ? [] : errors };
}

module.exports = validateUser;