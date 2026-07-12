import { configure } from 'mobx';
import { AppRegistry, Text, TextInput } from 'react-native';
import AppPersonal from './App';
import { PERSONAL } from '../../../app.json';
configure({ useProxies: 'never' });
Text.defaultProps = Object.assign({}, Text.defaultProps, {
  allowFontScaling: false,
});
TextInput.defaultProps = Object.assign({}, TextInput.defaultProps, {
  defaultProps: false,
});
AppRegistry.registerComponent(PERSONAL.name, () => AppPersonal);
