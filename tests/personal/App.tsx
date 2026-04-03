/* eslint-disable prettier/prettier */
import React from 'react';
import { Dimensions, View, DeviceEventEmitter, StatusBar } from 'react-native';
import {
  Provider,
  PlatformUtils,
  envService,
  ServiceProps,
  setCustomText,
  captureException,
  fontStore,
  DarkStore,
  AppStore,
  getRnProductComponentSizeEnable,
  TabsTopStore,
  appIdStore,
  RecordUtils,
  E2EIdStore,
  DeviceUtils,
  Bridge,
  BBD_KEY,
  configStore,
  CommonUtils,
  PAGE_TYPE_E2EID,
  getLanguage,
  PAGE_TYPE,
} from '@hw-vmall/vrn-basic-comp';
import { ErrorBoundary } from '@hw-vmall/vrn-bussiness-comp';
import { Provider as MobxProvider, observer } from 'mobx-react';
import { I18nextProvider } from 'react-i18next';
import { enableScreens } from 'react-native-screens';
import { ImgArrayUpdata } from '../../assets/ImgArray';
import { handleI18nextNative } from '../../common/i18-module/utils';
import { default as Personal } from './pages';

enableScreens(false);
setCustomText();
@observer
class AppPersonal extends React.Component<any, any> {
  eventListener: any;
  listenerNative: any;
  pageId: string;
  isAuto = false;
  darkDate: any;
  darkMode: any;
  sizeChangeListener: any;
  statusBarListener: any;
  constructor(props: any) {
    super(props);
    // apk在native侧生成了对应的e2eId信息，iOS需要自己生成
    const apkParams = { e2eId: this.props.e2eId, spanId: this.props.parentSpanId };
    CommonUtils.storeE2eId(PAGE_TYPE_E2EID.personal, PlatformUtils.isAndroid() ? false : true, apkParams);
    const e2eIdInfo = E2EIdStore.pageTypeE2EIdSpanId[E2EIdStore.curPageType];
    const iosParams = { e2eId: e2eIdInfo.e2eId, spanId: e2eIdInfo.parentSpanId };
    E2EIdStore.setResidentPageE2EId(PAGE_TYPE_E2EID.personal, PlatformUtils.isAndroid() ? apkParams : iosParams);
    appIdStore.setIsPreload(props.isPreInstalledPackage);
    DeviceUtils.deviceStore(props);
    AppStore.setIsLogin(props.isLogin);
    this.pageId = this.props.pageId;
    this.state = {
      updateEnv: false,
      isJump: false,
      pageId: '',
      isWeb: true,
      defaultStyle: 'default',
      DarkStyle: false,
      width: Dimensions.get('window').width,
      statusBarHeight: props.statusBarHeight !== undefined ? props.statusBarHeight : StatusBar.currentHeight || 0,
    };
    this.sizeChangeListener = DeviceUtils.getWidthHeightChange(this.getWidthAndHeight, PAGE_TYPE.homePage);
    this._onLayout = this._onLayout.bind(this);
    // 异常捕获
    captureException('Personal');
  }

  componentDidMount() {
    if (PlatformUtils.isApp()) {
      this.registerListeners();
      // 系统字体跟随倍率获取
      const isAndroidHarmony = PlatformUtils.isAndroid() || PlatformUtils.isHarmony();
      if (isAndroidHarmony) {
        appIdStore.deviceType || appIdStore.getDeviceType();
        fontStore.setFontMutiple(this.props.fontSize);
        fontStore.setDensityScale(this.props.densityScale);
      }
      getRnProductComponentSizeEnable();
      DarkStore.setpageId(this.props.pageId);
      fontStore.setVersion(JSON.parse(this.props.networkFields)?.version);
      this.setState({
        isWeb: false,
      });

      let envProps: ServiceProps;
      envProps = this.props.apiEnv && JSON.parse(this.props.apiEnv);
      let userAbTest = this.getUserAbTest();
      envProps.strategies = userAbTest || '';
      const pageId: string = this.props.pageId?.toString();
      this.getDarkDate();

      /**
       * 深色模式 开关
       * "darkMode":"Y",  深色模式 Y：打开，N:关闭
       *
       */
      this.darkMode = this.props.darkMode;
      const isDarkModeY =
        this.darkMode && JSON.parse(this.darkMode) && this.darkDate.darkMode && this.darkDate.darkMode === 'Y';
      if (isDarkModeY) {
        this.setState({
          defaultStyle: 'huawei_dark',
          DarkStyle: true,
        });
        DarkStore.setDarkBool(this.darkMode);
      }
      envProps.pageId = pageId;
      appIdStore.setApkPackageName(this.props.appPackageName);
      appIdStore.setTid(this.props.tid);
      envService(envProps);
      ImgArrayUpdata();
      this.setState({
        updateEnv: true,
        pageId: pageId,
      });

      /**
       * 监听页面加载
       */
      this.listenerNative = DeviceEventEmitter.addListener('NativeCallAction', (event) => {
        // 深色模式
        const { service, action, tabname, tabindex } = event;
        const setDarkMode = service === 'page' && action === 'setDarkMode';
        const isDarkMode = event.param?.isDarkMode;
        if (setDarkMode) {
          this.darkMode = isDarkMode ? true : false;
          DarkStore.setDarkBool(this.darkMode);
          this.setState({
            defaultStyle: this.darkMode ? 'huawei_dark' : 'default',
            DarkStyle: this.darkMode,
          });
        }
        if (tabname && tabindex) {
          TabsTopStore.setTabNameIndex(tabname || '', isNaN(Number(tabindex)) ? 0 : Number(tabindex));
        }
      });
    }
  }

  private registerListeners() {
    this.statusBarListener = PlatformUtils.isHarmony() && DeviceUtils.getBarHeight((statusHeight: number) => {
      if (statusHeight !== undefined && statusHeight !== this.state.statusBarHeight) {
        this.setState({
          statusBarHeight: statusHeight,
        });
      }
    });
  }

  private getDarkDate() {
    this.darkDate =
      this.props.darkConfigInfo &&
      (PlatformUtils.isAndroid() || PlatformUtils.isHarmony()
        ? JSON.parse(JSON.parse(this.props.darkConfigInfo))
        : JSON.parse(this.props.darkConfigInfo));
  }

  private getUserAbTest() {
    let userAbTest = (this.props.userAbTest && JSON.parse(this.props.userAbTest)) || [];
    userAbTest = userAbTest
      ?.map((item) => {
        return item.strategyId || '';
      })
      ?.join(',');
    return userAbTest;
  }

  getWidthAndHeight = (width: number, height: number) => {
    if (Math.abs(this.state.width - width) < 1) {
      return;
    }
    this.setState({
      width,
      height,
    });
  };

  _onLayout(event) {
    const eventWidth = event.nativeEvent.layout.width;
    const eventHeight = event.nativeEvent.layout.height;
    this.getWidthAndHeight(eventWidth, eventHeight);
  }

  componentWillUnmount() {
    this.listenerNative && this.listenerNative.remove();
    this.eventListener && this.eventListener.remove();
    this.sizeChangeListener && this.sizeChangeListener.remove();
    this.statusBarListener && this.statusBarListener.remove();
    delete E2EIdStore.setResidentPageE2EId[PAGE_TYPE_E2EID.personal];
  }

  render() {
    const { RnPromptMsg } = this.props;
    const lang = getLanguage(this.props);
    const i18next = handleI18nextNative(RnPromptMsg, lang);
    const DarkStyle =
      !DarkStore.QMbool &&
      (PlatformUtils.isIOS() ? this.state.DarkStyle : this.darkMode && this.darkDate?.darkMode === 'Y');
    DarkStore.setDarkBool(DarkStyle);
    RecordUtils.info('personal', 'enableAdvancedFeature=' + this.props.enableAdvancedFeature);
    return this.state.updateEnv && i18next ? (
      <Provider theme={DarkStyle ? 'huawei_dark' : 'default'} width={this.state.width} height={this.state.height}>
        <View onLayout={this._onLayout} style={{ position: 'absolute', width: '100%', height: '100%' }} />
        <MobxProvider store={AppStore}>
          <I18nextProvider i18n={i18next}>
            <ErrorBoundary>
              <Personal
                {...this.props}
                {...this.state}
                {...(PlatformUtils.isHarmony() && {isLogin : AppStore.isLogin})} // 单框架初始从props取的登录状态可能不对，需要监听AppStore里的变化
                pageId={this.props.pageId}
                pageAlias={this.props.pn}
                DarkStyle={DarkStyle}
              />
            </ErrorBoundary>
          </I18nextProvider>
        </MobxProvider>
      </Provider>
    ) : (
      <View onLayout={this._onLayout} />
    );
  }
}

export default AppPersonal;
