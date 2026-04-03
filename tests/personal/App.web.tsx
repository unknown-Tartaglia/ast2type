import React from 'react';
import { Platform, View } from 'react-native';
import {
  EventTracking,
  envService,
  Service,
  env,
  AppStore,
  ApmUtils,
  CommonUtils,
  PAGE_TYPE_E2EID,
} from '@hw-vmall/vrn-basic-comp';
import { ErrorBoundary } from '@hw-vmall/vrn-bussiness-comp';
import { I18nextProvider } from 'react-i18next';
import { default as Personal } from './pages/personalpage';
import { Provider } from 'mobx-react';
import { handleI18next } from '../../common/i18-module/utils';

let beforeUnloadTimePersonal = 0;
let gapTimePersonal = 0;
const isFireFox =
  Platform.OS === 'web' && navigator?.userAgent?.indexOf('Firefox') > -1;
class AppPersonal extends React.Component<any, any> {
  eventListener: any;
  _timer: any;
  constructor(props: any) {
    super(props);
    this.state = {
      updateEnv: false,
      isJump: false,
      pageId: '',
      isWeb: true,
      lang: '',
      defaultStyle: 'default',
      DarkStyle: false,
    };
    // 存储页面e2eId
    CommonUtils.storeE2eId(PAGE_TYPE_E2EID.personal, true);
    // APM埋点初始化，合并querySystemConfigByCar
    ApmUtils.apmMonitorInitWithAllBdd();
  }

  unload() {
    gapTimePersonal = new Date().getTime() - beforeUnloadTimePersonal;
    if (gapTimePersonal <= 5) {
      EventTracking.execReportData('', true);
    }
  }
  beforeunload(_e: any) {
    beforeUnloadTimePersonal = new Date().getTime();
    if (isFireFox) {
      EventTracking.execReportData('', true);
    }
  }

  componentDidMount() {
    if (Platform.OS === 'web') {
      envService(env);
      this.setState({
        lang: env.defaultLang,
        updateEnv: true,
      });
      window.addEventListener('unload', this.unload);
      window.addEventListener('beforeunload', this.beforeunload);
      this._startReportTimerPersonal();
    }
  }

  _startReportTimerPersonal() {
    this._stopReportTimerPersonal();
    this._timer = setInterval(() => {
      EventTracking.execReportData('', true);
    }, Service.reportTimeGap | 20000);
  }

  _stopReportTimerPersonal() {
    this._timer && clearInterval(this._timer);
  }

  componentWillUnmount() {
    this.eventListener && this.eventListener.remove();
    this._stopReportTimerPersonal();
  }

  render() {
    const i18next = handleI18next();
    return this.state.updateEnv && i18next ? (
      <Provider store={AppStore}>
        <I18nextProvider i18n={i18next}>
          <ErrorBoundary>
            <Personal />
          </ErrorBoundary>
        </I18nextProvider>
      </Provider>
    ) : (
      <View />
    );
  }
}
export default AppPersonal;
