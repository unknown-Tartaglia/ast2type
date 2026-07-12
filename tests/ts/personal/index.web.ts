import { configure } from 'mobx';
import 'react-app-polyfill/ie11';
import 'react-app-polyfill/stable';
import { AppRegistry } from 'react-native';
import App_Mine from './App.web';
// @ts-expect-error 忽略TS检查
import { PERSONAL } from '../../../app.json';
import ResizeObserver from 'resize-observer-polyfill';
window.ResizeObserver = ResizeObserver;
configure({ useProxies: 'never' });

AppRegistry.registerComponent(PERSONAL.name, () => App_Mine);

AppRegistry.runApplication(PERSONAL.name, {
  initialProps: {},
  rootTag: document.getElementById('react-root'),
});
